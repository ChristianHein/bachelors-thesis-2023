/*
 * Copyright (c) 1995, 2020, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

// Using KeY 2.11.0 (internal: 208396f69e) for verification.
//
// Using proof search strategy preset "Java verif. std.".
//
// Taclet settings used (unless stated otherwise):
// - assertions:on
// - intRules:javaSemantics
// - runtimeExceptions:allow
// Other taclet settings are kept on default.

/*
package java.util;
*/

// [Added import so that KeY's contract for Arrays::copyOf is loaded]
import java.util.Arrays;

public class BitSet /* implements Cloneable, java.io.Serializable */ {
    /* ****************************************** */
    /* Internally overriden external dependencies */
    /* (code largely copied from OpenJDK)         */
    /* ****************************************** */

    private final static class Math {
        /*@ public normal_behavior
          @  ensures \result == a || \result == b;
          @  ensures \result >= a && \result >= b;
          @  assignable \strictly_nothing;
          @*/
        public static int max(int a, int b) {
            return (a >= b) ? a : b;
        }

        /*@ public normal_behavior
          @  ensures \result == a || \result == b;
          @  ensures \result <= a && \result <= b;
          @  assignable \strictly_nothing;
          @*/
        public static int min(int a, int b) {
            return (a <= b) ? a : b;
        }
    }

    private final static class System {
        // [Own implementation used (OpenJDK uses "native" implementation)]
        // [Incomplete specification. Sufficient for BitSet]
        /*@ public normal_behavior
          @  requires srcPos == 0;
          @  requires destPos == 0;
          @  requires 0 <= length && length <= dest.length
          @                       && length <= src.length;
          @  ensures (\forall int i; 0 <= i && i < length;
          @               dest[i] == src[i]);
          @  assignable dest[0 .. length - 1];
          @*/
        public static void arraycopy(long[] src,  int  srcPos,
                                     long[] dest, int destPos,
                                     int length) {
            /*@ maintaining 0 <= i && i <= length;
              @ maintaining (\forall int j; 0 <= j && j < i;
              @                  dest[j] == src[j]);
              @ maintaining (\forall int j; i <= j && j < length;
              @                  \old(dest[j]) == dest[j]);
              @ decreasing length - i;
              @ assignable dest[0 .. length - 1];
              @*/
            for (int i = 0; i < length; i++) {
                dest[i] = src[i];
            }
        }
    }

    private final static class Long {
        public static final long MIN_VALUE = 0x8000000000000000L;
        public static final long MAX_VALUE = 0x7fffffffffffffffL;
        public static final int SIZE = 64;

        /*@ public normal_behavior
          @  ensures 0 <= \result && \result <= Long.SIZE;
          @  ensures (\forall int index;
          @               Long.SIZE > index && index >= (Long.SIZE - \result);
          @               \dl_bitAt(i, index) == 0);
          @  ensures \result != Long.SIZE
          @              ==> \dl_bitAt(i, Long.SIZE - (\result + 1)) == 1;
          @  assignable \strictly_nothing;
          @*/
        public static int numberOfLeadingZeros(long i) {
            int x = (int)(i >>> 32);
            return x == 0 ? 32 + Integer.numberOfLeadingZeros((int)i)
                    : Integer.numberOfLeadingZeros(x);
        }
    }

    public final static class Integer {
        public static final int MIN_VALUE = 0x80000000;
        public static final int MAX_VALUE = 0x7fffffff;
        public static final int SIZE = 32;

        /*@ public normal_behavior
          @  ensures 0 <= \result && \result <= Integer.SIZE;
          @  ensures (\forall int index;
          @               Integer.SIZE > index && index >= (Integer.SIZE - \result);
          @               \dl_bitAt(i, index) == 0);
          @  ensures \result != Integer.SIZE
          @              ==> \dl_bitAt(i, Integer.SIZE - (\result + 1)) == 1;
          @  assignable \strictly_nothing;
          @*/
        public static int numberOfLeadingZeros(int i) {
            if (i <= 0)
                return i == 0 ? 32 : 0;
            int n = 31;
            if (i >= 1 << 16) { n -= 16; i >>>= 16; }
            if (i >= 1 <<  8) { n -=  8; i >>>=  8; }
            if (i >= 1 <<  4) { n -=  4; i >>>=  4; }
            if (i >= 1 <<  2) { n -=  2; i >>>=  2; }
            return n - (i >>> 1);
        }
    }

    private static final int ADDRESS_BITS_PER_WORD = 6;
    private static final int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;

    //@ ghost \free iSet;

    /*@ public model \locset footprint;
      @ public represents footprint = \set_union(this.*, this.words.*);
      @ public accessible footprint: footprint;
      @*/

    /*@ public invariant 0 <= wordsInUse && wordsInUse <= words.length;
      @ public invariant wordsInUse != 0 ==> words[wordsInUse - 1] != 0;
      @ public invariant (\forall int i; wordsInUse <= i && i < words.length;
      @                       words[i] == 0);
      @ public invariant (\forall int wordIndex, bitIndex;
      @                       0 <= wordIndex && wordIndex < wordsInUse
      @                           && 0 <= bitIndex && bitIndex < BITS_PER_WORD;
      @                       \dl_in((long)wordIndex * BITS_PER_WORD + bitIndex, iSet)
      @                           <==> \dl_bitAt(words[wordIndex], bitIndex) == 1);
      @ public invariant (\forall long x; \dl_in(x, iSet);
      @                       0 <= x && x < (long)wordsInUse * BITS_PER_WORD);
      @
      @ // Necessary because KeY cannot prove this on its own. See issue #1271.
      @ public invariant (\forall int i;
      @                       0 <= i && i < words.length;
      @                       Long.MIN_VALUE <= words[i] && words[i] <= Long.MAX_VALUE);
      @
      @ public accessible \inv: footprint;
      @*/

    private long[] words;

    private transient int wordsInUse = 0;

    // [Never read]
    private transient boolean sizeIsSticky = false;

    /*@ private normal_behavior
      @  requires -1 <= bitIndex; // initWords(int) may call this method with -1
      @  ensures bitIndex == -1 ==> \result == -1;
      @  ensures bitIndex != -1 ==> \result == bitIndex / BITS_PER_WORD;
      @  assignable \strictly_nothing;
      @*/
    /*@ helper @*/
    private static int wordIndex(int bitIndex) {
        return bitIndex >> ADDRESS_BITS_PER_WORD;
    }

    /*@ private normal_behavior
      @  requires words != null;
      @  requires 0 <= wordsInUse && wordsInUse <= words.length;
      @  requires wordsInUse == 0 || words[wordsInUse - 1] != 0;
      @  requires wordsInUse >= 0 && wordsInUse <= words.length;
      @  requires wordsInUse == words.length || words[wordsInUse] == 0;
      @  assignable \strictly_nothing;
      @
      @ also
      @
      @ private exceptional_behavior
      @  requires words != null;
      @  requires !(0 <= wordsInUse && wordsInUse <= words.length)
      @        || !(wordsInUse == 0 || words[wordsInUse - 1] != 0)
      @        || !(wordsInUse >= 0 && wordsInUse <= words.length)
      @        || !(wordsInUse == words.length || words[wordsInUse] == 0);
      @  signals_only AssertionError, ArrayIndexOutOfBoundsException;
      @  signals (ArrayIndexOutOfBoundsException)
      @      wordsInUse < 0 || words.length < wordsInUse;
      @  signals (AssertionError) true;
      @  assignable \nothing;
      @*/
    /*@ helper @*/
    private void checkInvariants() {
        assert(wordsInUse == 0 || words[wordsInUse - 1] != 0);
        assert(wordsInUse >= 0 && wordsInUse <= words.length);
        assert(wordsInUse == words.length || words[wordsInUse] == 0);
    }

    /*@ private normal_behavior
      @  requires words != null;
      @  requires 0 <= wordsInUse && wordsInUse <= words.length;
      @  requires (\forall int i; wordsInUse <= i && i < words.length;
      @                words[i] == 0);
      @  ensures \old(wordsInUse) >= wordsInUse;
      @  ensures 0 <= wordsInUse && wordsInUse <= words.length;
      @  ensures wordsInUse != 0 ==> words[wordsInUse - 1] != 0;
      @  ensures (\forall int i; wordsInUse <= i && i < words.length;
      @               words[i] == 0);
      @  assignable wordsInUse;
      @*/
    /*@ helper @*/
    private void recalculateWordsInUse() {
        int i;
        /*@ maintaining -1 <= i && i < wordsInUse;
          @ maintaining (\forall int j; i < j && j <= wordsInUse - 1;
          @                  words[j] == 0);
          @ decreasing i + 1;
          @ assignable \strictly_nothing;
          @*/
        for (i = wordsInUse-1; i >= 0; i--)
            if (words[i] != 0)
                break;

        wordsInUse = i+1;
    }

    /*@ public normal_behavior
      @  ensures iSet == \dl_iset_empty();
      @  ensures \fresh(footprint);
      @  assignable \nothing;
      @*/
    public BitSet() {
        initWords(BITS_PER_WORD);
        sizeIsSticky = false;
    }

    /*@ private normal_behavior
      @  requires 0 <= nbits;
      @  ensures words != null;
      @  ensures words.length == wordIndex(nbits - 1) + 1;
      @  ensures (\forall int i; 0 <= i && i < words.length;
      @               words[i] == 0);
      @  ensures iSet == \dl_iset_empty();
      @  ensures \fresh(words);
      @  assignable words, iSet;
      @*/
    /*@ helper @*/
    private void initWords(int nbits) {
        words = new long[wordIndex(nbits-1) + 1];
        //@ set iSet = \dl_iset_empty();
    }

    /*@ private normal_behavior
      @  requires words != null;
      @  requires words.length >= wordsRequired;
      @  assignable \strictly_nothing;
      @
      @ also
      @
      @ private normal_behavior
      @  requires words != null;
      @  requires words.length < wordsRequired;
      @  ensures words != null;
      @  ensures words.length > \old(words.length);
      @  ensures words.length >= wordsRequired;
      @  ensures (\forall int i; 0 <= i && i < \old(words.length);
      @               words[i] == \old(words[i]));
      @  ensures (\forall int i; \old(words.length) <= i && i < words.length;
      @               words[i] == 0);
      @  ensures sizeIsSticky == false;
      @  ensures \fresh(words);
      @  assignable words, sizeIsSticky;
      @*/
    /*@ helper @*/
    private void ensureCapacity(int wordsRequired) {
        if (words.length < wordsRequired) {
            int request = Math.max(2 * words.length, wordsRequired);
            words = Arrays.copyOf(words, request);
            sizeIsSticky = false;
        }
    }

    /*@ private normal_behavior
      @  requires words != null;
      @  requires wordsInUse > wordIndex;
      @  assignable \strictly_nothing;
      @
      @ also
      @
      @ private normal_behavior
      @  requires words != null;
      @  requires wordsInUse <= wordIndex && wordIndex < words.length;
      @  ensures wordsInUse == wordIndex + 1;
      @  assignable wordsInUse;
      @
      @ also
      @
      @ private normal_behavior
      @  requires words != null;
      @  requires wordsInUse <= words.length;
      @  requires words.length <= wordIndex && wordIndex != Integer.MAX_VALUE;
      @  ensures words != null;
      @  ensures \old(words.length) < words.length;
      @  ensures words.length > wordIndex;
      @  ensures (\forall int i; 0 <= i && i < \old(words.length);
      @               words[i] == \old(words[i]));
      @  ensures (\forall int i; \old(words.length) <= i && i < words.length;
      @               words[i] == 0);
      @  ensures wordsInUse == wordIndex + 1;
      @  ensures sizeIsSticky == false;
      @  ensures \fresh(words);
      @  assignable words, wordsInUse, sizeIsSticky;
      @*/
    /*@ helper @*/
    private void expandTo(int wordIndex) {
        int wordsRequired = wordIndex+1;
        if (wordsInUse < wordsRequired) {
            ensureCapacity(wordsRequired);
            wordsInUse = wordsRequired;
        }
    }

    /*@ public normal_behavior
      @  requires 0 <= bitIndex;
      @  ensures  \dl_in(bitIndex, \old(iSet)) ==> !\dl_in(bitIndex, iSet);
      @  ensures !\dl_in(bitIndex, \old(iSet)) ==>  \dl_in(bitIndex, iSet);
      @  ensures (\forall int x; 0 <= x && x != bitIndex;
      @               \dl_in(x, \old(iSet)) == \dl_in(x, iSet));
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @
      @ also
      @
      @ public exceptional_behavior
      @  requires bitIndex < 0;
      @  signals (IndexOutOfBoundsException) true;
      @  signals_only IndexOutOfBoundsException;
      @  assignable \nothing;
      @*/
    public void flip(int bitIndex) {
        if (bitIndex < 0)
            throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);

        int wordIndex = wordIndex(bitIndex);
        expandTo(wordIndex);

        words[wordIndex] ^= (1L << bitIndex);
        /*@ set iSet = \dl_in(bitIndex, iSet)
                           ? \dl_iset_remove(bitIndex, iSet)
                           : \dl_iset_insert(bitIndex, iSet);
         */

        recalculateWordsInUse();
        checkInvariants();
    }

    /*@ public normal_behavior
      @  requires 0 <= bitIndex;
      @  ensures \dl_in(bitIndex, iSet);
      @  ensures (\forall int x; 0 <= x && x != bitIndex;
      @               \dl_in(x, iSet) == \dl_in(x, \old(iSet)));
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @
      @ also
      @
      @ public exceptional_behavior
      @  requires bitIndex < 0;
      @  signals (IndexOutOfBoundsException) true;
      @  signals_only IndexOutOfBoundsException;
      @  assignable \nothing;
      @*/
    public void set(int bitIndex) {
        if (bitIndex < 0)
            throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);

        int wordIndex = wordIndex(bitIndex);
        expandTo(wordIndex);

        words[wordIndex] = setBitAt(words[wordIndex], bitIndex % BITS_PER_WORD);
        //@ set iSet = \dl_iset_insert(bitIndex, iSet);

        checkInvariants();
    }

    /*@ private normal_behavior
      @  requires 0 <= bitIndex && bitIndex < Long.SIZE;
      @  ensures \dl_bitAt(\result, bitIndex) == 1;
      @  ensures (\forall int i;
      @               0 <= i && i != bitIndex && i < Long.SIZE;
      @               \dl_bitAt(\result, i) == \dl_bitAt(word, i));
      @  assignable \strictly_nothing;
      @*/
    /*@ helper @*/
    private static long setBitAt(long word, int bitIndex) {
        return word | (1L << bitIndex);
    }

    /*@ public normal_behavior
      @  requires 0 <= bitIndex;
      @  ensures !\dl_in(bitIndex, iSet);
      @  ensures (\forall int x; 0 <= x && x != bitIndex;
      @               \dl_in(x, iSet) == \dl_in(x, \old(iSet)));
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @
      @ also
      @
      @ public exceptional_behavior
      @  requires bitIndex < 0;
      @  signals (IndexOutOfBoundsException) true;
      @  signals_only IndexOutOfBoundsException;
      @  assignable \nothing;
      @*/
    public void clear(int bitIndex) {
        if (bitIndex < 0)
            throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);

        int wordIndex = wordIndex(bitIndex);
        if (wordIndex >= wordsInUse)
            return;

        words[wordIndex] &= ~(1L << bitIndex);
        //@ set iSet = \dl_iset_remove(bitIndex, iSet);

        recalculateWordsInUse();
        checkInvariants();
    }

    /*@ public normal_behavior
      @  requires 0 <= bitIndex;
      @  ensures \result == \dl_in(bitIndex, iSet);
      @  assignable \strictly_nothing;
      @
      @ also
      @
      @ public exceptional_behavior
      @  requires bitIndex < 0;
      @  signals (IndexOutOfBoundsException) true;
      @  signals_only IndexOutOfBoundsException;
      @  assignable \nothing;
      @*/
    public boolean get(int bitIndex) {
        if (bitIndex < 0)
            throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);

        checkInvariants();

        int wordIndex = wordIndex(bitIndex);
        return (wordIndex < wordsInUse)
            && (getBitAt(words[wordIndex], bitIndex) != 0);
    }

    /*@ private normal_behavior
      @  requires 0 <= bitIndex;
      @  ensures \result == 0 || \result == 1;
      @  ensures \result == \dl_bitAt(word, bitIndex % Long.SIZE);
      @  assignable \strictly_nothing;
      @*/
    /*@ helper @*/
    private static int getBitAt(long word, int bitIndex) {
        return (word & (1L << bitIndex)) == 0 ? 0 : 1;
    }

    /*@ public normal_behavior
      @  ensures \result == (iSet == \dl_iset_empty()
      @                      ? 0 : \dl_moduloInt(\dl_iset_max(iSet) + 1));
      @  assignable \strictly_nothing;
      @*/
    public int length() {
        if (wordsInUse == 0)
            return 0;

        return BITS_PER_WORD * (wordsInUse - 1) +
            (BITS_PER_WORD - Long.numberOfLeadingZeros(words[wordsInUse - 1]));
    }

    /*@ public normal_behavior
      @  requires \invariant_for(set);
      @  requires \disjoint(footprint, set.footprint);
      @  ensures iSet == \dl_iset_intersect(\old(iSet), set.iSet);
      @  ensures \invariant_for(set);
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @*/
    public void and(BitSet set) {
        if (this == set)
            return;

        /*@ maintaining set.wordsInUse <= wordsInUse
          @             && wordsInUse <= \old(wordsInUse);
          @ maintaining (\forall int i;
          @                  \old(wordsInUse) - 1 <= i && i <= wordsInUse;
          @                  words[i] == 0);
          @ decreasing wordsInUse;
          @ assignable wordsInUse, words[\old(wordsInUse) - 1 .. set.wordsInUse];
          @*/
        while (wordsInUse > set.wordsInUse)
            words[--wordsInUse] = 0;

        /*@ maintaining 0 <= i && i <= wordsInUse;
          @ maintaining (\forall int j;
          @                  0 <= j && j < i;
          @                  words[j] == (\old(words[j]) & set.words[j]));
          @ decreasing wordsInUse - i;
          @ assignable words[0 .. wordsInUse - 1];
          @*/
        for (int i = 0; i < wordsInUse; i++)
            words[i] &= set.words[i];

        //@ set iSet = \dl_iset_intersect(iSet, set.iSet);

        recalculateWordsInUse();
        checkInvariants();
    }

    /*@ public normal_behavior
      @  requires \invariant_for(set);
      @  requires \disjoint(footprint, set.footprint);
      @  ensures iSet == \dl_iset_union(\old(iSet), set.iSet);
      @  ensures \invariant_for(set);
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @*/
    public void or(BitSet set) {
        if (this == set)
            return;

        int wordsInCommon = Math.min(wordsInUse, set.wordsInUse);

        if (wordsInUse < set.wordsInUse) {
            ensureCapacity(set.wordsInUse);
            wordsInUse = set.wordsInUse;
        }

        /*@ maintaining 0 <= i && i <= wordsInCommon;
          @ maintaining (\forall int j;
          @                  0 <= j && j < i;
          @                  words[j] == (\old(words[j]) | set.words[j]));
          @ decreasing wordsInCommon - i;
          @ assignable words[0 .. wordsInCommon - 1];
          @*/
        for (int i = 0; i < wordsInCommon; i++)
            words[i] |= set.words[i];

        //@ set iSet = \dl_iset_union(iSet, set.iSet);

        if (wordsInCommon < set.wordsInUse)
            System.arraycopy(set.words, wordsInCommon,
                             words, wordsInCommon,
                             wordsInUse - wordsInCommon);

        checkInvariants();
    }

    /*@ public normal_behavior
      @  requires \invariant_for(set);
      @  requires \disjoint(footprint, set.footprint);
      @  ensures iSet == \dl_iset_symmetricDifference(\old(iSet), set.iSet);
      @  ensures \invariant_for(set);
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @*/
    public void xor(BitSet set) {
        int wordsInCommon = Math.min(wordsInUse, set.wordsInUse);

        if (wordsInUse < set.wordsInUse) {
            ensureCapacity(set.wordsInUse);
            wordsInUse = set.wordsInUse;
        }

        /*@ maintaining 0 <= i && i <= wordsInCommon;
          @ maintaining (\forall int j;
          @                  0 <= j && j < i;
          @                  words[j] == (\old(words[j]) ^ set.words[j]));
          @ decreasing wordsInCommon - i;
          @ assignable words[0 .. wordsInCommon - 1];
          @*/
        for (int i = 0; i < wordsInCommon; i++)
            words[i] ^= set.words[i];

        //@ set iSet = \dl_iset_symmetricDifference(iSet, set.iSet);

        if (wordsInCommon < set.wordsInUse)
            System.arraycopy(set.words, wordsInCommon,
                             words, wordsInCommon,
                             set.wordsInUse - wordsInCommon);

        recalculateWordsInUse();
        checkInvariants();
    }

    /*@ public normal_behavior
      @  requires \invariant_for(set);
      @  requires \disjoint(footprint, set.footprint);
      @  ensures iSet == \dl_iset_difference(\old(iSet), set.iSet);
      @  ensures \invariant_for(set);
      @  ensures \new_elems_fresh(footprint);
      @  assignable footprint;
      @*/
    public void andNot(BitSet set) {
        /* @ maintaining 0 <= i && i <= Math.min(wordsInUse, set.wordsInUse);
           @ maintaining (\forall int j;
           @                  0 <= j && j < i;
           @                  words[j] == (\old(words[j]) & ~set.words[j]));
           @ decreasing Math.min(wordsInUse, set.wordsInUse) - i;
           @ assignable words[0 .. Math.min(wordsInUse, set.wordsInUse) - 1];
           @*/
        for (int i = Math.min(wordsInUse, set.wordsInUse) - 1; i >= 0; i--)
            words[i] &= ~set.words[i];

        //@ set iSet = \dl_iset_difference(iSet, set.iSet);

        recalculateWordsInUse();
        checkInvariants();
    }
}
 
