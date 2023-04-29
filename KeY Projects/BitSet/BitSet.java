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

/*
import java.io.*;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.LongBuffer;
import java.util.function.IntConsumer;
import java.util.stream.IntStream;
import java.util.stream.StreamSupport;
*/

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

    private final static class Arrays {
        // [Incomplete specification. Sufficient for BitSet]
        // [Note: Use `Query treatment: On/Restricted`.]
        /*@ public normal_behavior
          @  requires original != null;
          @  requires 0 <= newLength;
          @  ensures \result.length == newLength;
          @  ensures (\forall int i;
          @               0 <= i && i < Math.min(original.length, newLength);
          @               \result[i] == original[i]);
          @  ensures (\forall int i;
          @               Math.min(original.length, newLength) <= i && i < \result.length;
          @               \result[i] == 0);
          @  assignable \nothing;
          @
          @ also
          @
          @ public exceptional_behavior
          @  requires original == null || newLength < 0;
          @  signals (NegativeArraySizeException) newLength < 0;
          @  signals (NullPointerException) original == null && 0 <= newLength;
          @  signals_only NegativeArraySizeException, NullPointerException;
          @  assignable \nothing;
          @*/
        public static long[] copyOf(/*@ nullable @*/ long[] original, int newLength) {
            long[] copy = new long[newLength];
            System.arraycopy(original, 0, copy, 0,
                             Math.min(original.length, newLength));
            return copy;
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

        public static int numberOfTrailingZeros(long i) {
            int x = (int)i;
            return x == 0 ? 32 + Integer.numberOfTrailingZeros((int)(i >>> 32))
                    : Integer.numberOfTrailingZeros(x);
        }

        public static int bitCount(long i) {
            i = i - ((i >>> 1) & 0x5555555555555555L);
            i = (i & 0x3333333333333333L) + ((i >>> 2) & 0x3333333333333333L);
            i = (i + (i >>> 4)) & 0x0f0f0f0f0f0f0f0fL;
            i = i + (i >>> 8);
            i = i + (i >>> 16);
            i = i + (i >>> 32);
            return (int)i & 0x7f;
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

        public static int numberOfTrailingZeros(int i) {
            i = ~i & (i - 1);
            if (i <= 0) return i & 32;
            int n = 1;
            if (i > 1 << 16) { n += 16; i >>>= 16; }
            if (i > 1 <<  8) { n +=  8; i >>>=  8; }
            if (i > 1 <<  4) { n +=  4; i >>>=  4; }
            if (i > 1 <<  2) { n +=  2; i >>>=  2; }
            return n + (i >>> 1);
        }
    }

    /* **************************** */
    /* Start of "Must-have" section */
    /* **************************** */

    private static final int ADDRESS_BITS_PER_WORD = 6;
    private static final int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    private static final int BIT_INDEX_MASK = BITS_PER_WORD - 1;

    private static final long WORD_MASK = 0xffffffffffffffffL;

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

    // [Never read, except in commented out methods `clone`, `readObject`, and
    // `writeObject`]
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
      @  ensures \old(words.length) < words.length;
      @  ensures words.length >= wordsRequired;
      @  ensures (\forall int i; 0 <= i && i < \old(words.length);
      @               words[i] == \old(words[i]));
      @  ensures (\forall int i; \old(words.length) <= i && i < words.length;
      @               words[i] == 0);
      @  ensures sizeIsSticky == false;
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
      @  requires wordIndex < wordsInUse;
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
      @  ensures sizeIsSticky == false;
      @  ensures wordsInUse == wordIndex + 1;
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
      @  ensures \dl_bitAt(word, bitIndex) == 1;
      @  ensures (\forall int i;
      @               0 <= i && i != bitIndex && i < Long.SIZE;
      @               \dl_bitAt(\result, i) == \old(word, i));
      @  ensures \dl_bitAt(\result, bitIndex) == 1;
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
      @  ensures \result == \dl_bitAt(word, bitIndex % BITS_PER_WORD);
      @  assignable \strictly_nothing;
      @*/
    /*@ helper @*/
    private static int getBitAt(long word, int bitIndex) {
        return (word & (1L << bitIndex)) == 0 ? 0 : 1;
    }

    /*@ public normal_behavior
      @  ensures iSet == \dl_iset_empty() ==> \result == 0;
      @  ensures iSet != \dl_iset_empty()
      @      ==> \result == \dl_moduloInt(\dl_iset_max(iSet));
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

    /* ******************************* */
    /* Start of "Nice-to-have" section */
    /* ******************************* */

    public BitSet(int nbits) {
        if (nbits < 0)
            throw new NegativeArraySizeException("nbits < 0: " + nbits);

        initWords(nbits);
        sizeIsSticky = true;
    }

    private BitSet(long[] words) {
        this.words = words;
        this.wordsInUse = words.length;
        checkInvariants();
    }

    public static BitSet valueOf(long[] longs) {
        int n;
        for (n = longs.length; n > 0 && longs[n - 1] == 0; n--)
            ;
        return new BitSet(Arrays.copyOf(longs, n));
    }

    // [Providing an implementation for ByteBuffer and transitive dependencies
    // is too complex]
    /*
    public static BitSet valueOf(byte[] bytes) {
        return BitSet.valueOf(ByteBuffer.wrap(bytes));
    }
    */

    // [Providing an implementation for ByteBuffer and transitive dependencies
    // is too complex]
    /*
    public byte[] toByteArray() {
        int n = wordsInUse;
        if (n == 0)
            return new byte[0];
        int len = 8 * (n-1);
        for (long x = words[n - 1]; x != 0; x >>>= 8)
            len++;
        byte[] bytes = new byte[len];
        ByteBuffer bb = ByteBuffer.wrap(bytes).order(ByteOrder.LITTLE_ENDIAN);
        for (int i = 0; i < n - 1; i++)
            bb.putLong(words[i]);
        for (long x = words[n - 1]; x != 0; x >>>= 8)
            bb.put((byte) (x & 0xff));
        return bytes;
    }
    */

    public long[] toLongArray() {
        return Arrays.copyOf(words, wordsInUse);
    }

    private static void checkRange(int fromIndex, int toIndex) {
        if (fromIndex < 0)
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        if (toIndex < 0)
            throw new IndexOutOfBoundsException("toIndex < 0: " + toIndex);
        if (fromIndex > toIndex)
            throw new IndexOutOfBoundsException("fromIndex: " + fromIndex +
                                                " > toIndex: " + toIndex);
    }

    public void flip(int fromIndex, int toIndex) {
        checkRange(fromIndex, toIndex);

        if (fromIndex == toIndex)
            return;

        int startWordIndex = wordIndex(fromIndex);
        int endWordIndex   = wordIndex(toIndex - 1);
        expandTo(endWordIndex);

        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask  = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            words[startWordIndex] ^= (firstWordMask & lastWordMask);
        } else {
            words[startWordIndex] ^= firstWordMask;

            for (int i = startWordIndex+1; i < endWordIndex; i++)
                words[i] ^= WORD_MASK;

            words[endWordIndex] ^= lastWordMask;
        }

        recalculateWordsInUse();
        checkInvariants();
    }

    public void set(int bitIndex, boolean value) {
        if (value)
            set(bitIndex);
        else
            clear(bitIndex);
    }

    public void set(int fromIndex, int toIndex) {
        checkRange(fromIndex, toIndex);

        if (fromIndex == toIndex)
            return;

        int startWordIndex = wordIndex(fromIndex);
        int endWordIndex   = wordIndex(toIndex - 1);
        expandTo(endWordIndex);

        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask  = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            words[startWordIndex] |= (firstWordMask & lastWordMask);
        } else {
            words[startWordIndex] |= firstWordMask;

            for (int i = startWordIndex+1; i < endWordIndex; i++)
                words[i] = WORD_MASK;

            words[endWordIndex] |= lastWordMask;
        }

        checkInvariants();
    }

    public void set(int fromIndex, int toIndex, boolean value) {
        if (value)
            set(fromIndex, toIndex);
        else
            clear(fromIndex, toIndex);
    }

    public void clear(int fromIndex, int toIndex) {
        checkRange(fromIndex, toIndex);

        if (fromIndex == toIndex)
            return;

        int startWordIndex = wordIndex(fromIndex);
        if (startWordIndex >= wordsInUse)
            return;

        int endWordIndex = wordIndex(toIndex - 1);
        if (endWordIndex >= wordsInUse) {
            toIndex = length();
            endWordIndex = wordsInUse - 1;
        }

        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask  = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            words[startWordIndex] &= ~(firstWordMask & lastWordMask);
        } else {
            words[startWordIndex] &= ~firstWordMask;

            for (int i = startWordIndex+1; i < endWordIndex; i++)
                words[i] = 0;

            words[endWordIndex] &= ~lastWordMask;
        }

        recalculateWordsInUse();
        checkInvariants();
    }

    public void clear() {
        while (wordsInUse > 0)
            words[--wordsInUse] = 0;
    }

    public BitSet get(int fromIndex, int toIndex) {
        checkRange(fromIndex, toIndex);

        checkInvariants();

        int len = length();

        if (len <= fromIndex || fromIndex == toIndex)
            return new BitSet(0);

        if (toIndex > len)
            toIndex = len;

        BitSet result = new BitSet(toIndex - fromIndex);
        int targetWords = wordIndex(toIndex - fromIndex - 1) + 1;
        int sourceIndex = wordIndex(fromIndex);
        boolean wordAligned = ((fromIndex & BIT_INDEX_MASK) == 0);

        for (int i = 0; i < targetWords - 1; i++, sourceIndex++)
            result.words[i] = wordAligned ? words[sourceIndex] :
                (words[sourceIndex] >>> fromIndex) |
                (words[sourceIndex+1] << -fromIndex);

        long lastWordMask = WORD_MASK >>> -toIndex;
        result.words[targetWords - 1] =
            ((toIndex-1) & BIT_INDEX_MASK) < (fromIndex & BIT_INDEX_MASK)
            ?
            ((words[sourceIndex] >>> fromIndex) |
             (words[sourceIndex+1] & lastWordMask) << -fromIndex)
            :
            ((words[sourceIndex] & lastWordMask) >>> fromIndex);

        result.wordsInUse = targetWords;
        result.recalculateWordsInUse();
        result.checkInvariants();

        return result;
    }

    public int nextSetBit(int fromIndex) {
        if (fromIndex < 0)
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);

        checkInvariants();

        int u = wordIndex(fromIndex);
        if (u >= wordsInUse)
            return -1;

        long word = words[u] & (WORD_MASK << fromIndex);

        while (true) {
            if (word != 0)
                return (u * BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
            if (++u == wordsInUse)
                return -1;
            word = words[u];
        }
    }

    public int nextClearBit(int fromIndex) {
        if (fromIndex < 0)
            throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);

        checkInvariants();

        int u = wordIndex(fromIndex);
        if (u >= wordsInUse)
            return fromIndex;

        long word = ~words[u] & (WORD_MASK << fromIndex);

        while (true) {
            if (word != 0)
                return (u * BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
            if (++u == wordsInUse)
                return wordsInUse * BITS_PER_WORD;
            word = ~words[u];
        }
    }

    public int previousSetBit(int fromIndex) {
        if (fromIndex < 0) {
            if (fromIndex == -1)
                return -1;
            throw new IndexOutOfBoundsException(
                "fromIndex < -1: " + fromIndex);
        }

        checkInvariants();

        int u = wordIndex(fromIndex);
        if (u >= wordsInUse)
            return length() - 1;

        long word = words[u] & (WORD_MASK >>> -(fromIndex+1));

        while (true) {
            if (word != 0)
                return (u+1) * BITS_PER_WORD - 1 - Long.numberOfLeadingZeros(word);
            if (u-- == 0)
                return -1;
            word = words[u];
        }
    }

    public int previousClearBit(int fromIndex) {
        if (fromIndex < 0) {
            if (fromIndex == -1)
                return -1;
            throw new IndexOutOfBoundsException(
                "fromIndex < -1: " + fromIndex);
        }

        checkInvariants();

        int u = wordIndex(fromIndex);
        if (u >= wordsInUse)
            return fromIndex;

        long word = ~words[u] & (WORD_MASK >>> -(fromIndex+1));

        while (true) {
            if (word != 0)
                return (u+1) * BITS_PER_WORD -1 - Long.numberOfLeadingZeros(word);
            if (u-- == 0)
                return -1;
            word = ~words[u];
        }
    }

    public boolean isEmpty() {
        return wordsInUse == 0;
    }

    public boolean intersects(BitSet set) {
        for (int i = Math.min(wordsInUse, set.wordsInUse) - 1; i >= 0; i--)
            if ((words[i] & set.words[i]) != 0)
                return true;
        return false;
    }

    public int cardinality() {
        int sum = 0;
        for (int i = 0; i < wordsInUse; i++)
            sum += Long.bitCount(words[i]);
        return sum;
    }

    public int hashCode() {
        long h = 1234;
        for (int i = wordsInUse; --i >= 0; )
            h ^= words[i] * (i + 1);

        return (int)((h >> 32) ^ h);
    }

    public int size() {
        return words.length * BITS_PER_WORD;
    }

    /*@ public normal_behavior
      @  requires !(obj instanceof BitSet);
      @  ensures \result == false;
      @  assignable \strictly_nothing;
      @
      @ also
      @
      @ public normal_behavior
      @  requires obj instanceof BitSet;
      @  requires \invariant_for((BitSet)obj);
      @  ensures \result == (this.iSet == ((BitSet)obj).iSet);
      @  assignable \strictly_nothing;
      @*/
    public boolean equals(/*@ nullable @*/ Object obj) {
        if (!(obj instanceof BitSet))
            return false;
        if (this == obj)
            return true;

        BitSet set = (BitSet) obj;

        checkInvariants();
        set.checkInvariants();

        if (wordsInUse != set.wordsInUse)
            return false;

        /*@ maintaining 0 <= i && i <= wordsInUse;
          @ maintaining (\forall int j; 0 <= j && j < i;
          @                  words[j] == set.words[j]);
          @ decreasing wordsInUse - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < wordsInUse; i++)
            if (words[i] != set.words[i])
                return false;

        return true;
    }

    // [Never used, except in commented out methods `clone` and `writeObject`]
    private void trimToSize() {
        if (wordsInUse != words.length) {
            words = Arrays.copyOf(words, wordsInUse);
            checkInvariants();
        }
    }

    // [Providing an implementation for StringBuilder and transitive
    // dependencies may be too complex]
    /*
    public String toString() {
        checkInvariants();

        final int MAX_INITIAL_CAPACITY = Integer.MAX_VALUE - 8;
        int numBits = (wordsInUse > 128) ?
            cardinality() : wordsInUse * BITS_PER_WORD;
        int initialCapacity = (numBits <= (MAX_INITIAL_CAPACITY - 2) / 6) ?
            6 * numBits + 2 : MAX_INITIAL_CAPACITY;
        StringBuilder b = new StringBuilder(initialCapacity);
        b.append('{');

        int i = nextSetBit(0);
        if (i != -1) {
            b.append(i);
            while (true) {
                if (++i < 0) break;
                if ((i = nextSetBit(i)) < 0) break;
                int endOfRun = nextClearBit(i);
                do { b.append(", ").append(i); }
                while (++i != endOfRun);
            }
        }

        b.append('}');
        return b.toString();
    }
    */

    // [Never used, except in commented out method `stream`]
    private int nextSetBit(int fromIndex, int toWordIndex) {
        int u = wordIndex(fromIndex);
        if (u > toWordIndex)
            return -1;

        long word = words[u] & (WORD_MASK << fromIndex);

        while (true) {
            if (word != 0)
                return (u * BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
            if (++u > toWordIndex)
                return -1;
            word = words[u];
        }
    }

    /* ***************************** */
    /* Start of "Won't-have" section */
    /* ***************************** */

    /*
    @java.io.Serial
    private static final ObjectStreamField[] serialPersistentFields = {
        new ObjectStreamField("bits", long[].class),
    };
    */

    /*
    @java.io.Serial
    private static final long serialVersionUID = 7997698588986878753L;
    */

    /*
    public static BitSet valueOf(LongBuffer lb) {
        lb = lb.slice();
        int n;
        for (n = lb.remaining(); n > 0 && lb.get(n - 1) == 0; n--)
            ;
        long[] words = new long[n];
        lb.get(words);
        return new BitSet(words);
    }
    */

    /*
    public static BitSet valueOf(ByteBuffer bb) {
        bb = bb.slice().order(ByteOrder.LITTLE_ENDIAN);
        int n;
        for (n = bb.remaining(); n > 0 && bb.get(n - 1) == 0; n--)
            ;
        long[] words = new long[(n + 7) / 8];
        bb.limit(n);
        int i = 0;
        while (bb.remaining() >= 8)
            words[i++] = bb.getLong();
        for (int remaining = bb.remaining(), j = 0; j < remaining; j++)
            words[i] |= (bb.get() & 0xffL) << (8 * j);
        return new BitSet(words);
    }
    */

    /*
    public Object clone() {
        if (! sizeIsSticky)
            trimToSize();

        try {
            BitSet result = (BitSet) super.clone();
            result.words = words.clone();
            result.checkInvariants();
            return result;
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e);
        }
    }
    */

    /*
    @java.io.Serial
    private void writeObject(ObjectOutputStream s)
        throws IOException {

        checkInvariants();

        if (! sizeIsSticky)
            trimToSize();

        ObjectOutputStream.PutField fields = s.putFields();
        fields.put("bits", words);
        s.writeFields();
    }
    */

    /*
    @java.io.Serial
    private void readObject(ObjectInputStream s)
        throws IOException, ClassNotFoundException {

        ObjectInputStream.GetField fields = s.readFields();
        words = (long[]) fields.get("bits", null);

        wordsInUse = words.length;
        recalculateWordsInUse();
        sizeIsSticky = (words.length > 0 && words[words.length-1] == 0L);
        checkInvariants();
    }
    */

    /*
    public IntStream stream() {
        class BitSetSpliterator implements Spliterator.OfInt {
            private int index;
            private int fence;
            private int est;
            private boolean root;

            BitSetSpliterator(int origin, int fence, int est, boolean root) {
                this.index = origin;
                this.fence = fence;
                this.est = est;
                this.root = root;
            }

            private int getFence() {
                int hi;
                if ((hi = fence) < 0) {
                    hi = fence = (wordsInUse >= wordIndex(Integer.MAX_VALUE))
                                 ? Integer.MAX_VALUE
                                 : wordsInUse << ADDRESS_BITS_PER_WORD;
                    est = cardinality();
                    index = nextSetBit(0);
                }
                return hi;
            }

            @Override
            public boolean tryAdvance(IntConsumer action) {
                Objects.requireNonNull(action);

                int hi = getFence();
                int i = index;
                if (i < 0 || i >= hi) {
                    if (i == Integer.MAX_VALUE && hi == Integer.MAX_VALUE) {
                        index = -1;
                        action.accept(Integer.MAX_VALUE);
                        return true;
                    }
                    return false;
                }

                index = nextSetBit(i + 1, wordIndex(hi - 1));
                action.accept(i);
                return true;
            }

            @Override
            public void forEachRemaining(IntConsumer action) {
                Objects.requireNonNull(action);

                int hi = getFence();
                int i = index;
                index = -1;

                if (i >= 0 && i < hi) {
                    action.accept(i++);

                    int u = wordIndex(i);
                    int v = wordIndex(hi - 1);

                    words_loop:
                    for (; u <= v && i <= hi; u++, i = u << ADDRESS_BITS_PER_WORD) {
                        long word = words[u] & (WORD_MASK << i);
                        while (word != 0) {
                            i = (u << ADDRESS_BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
                            if (i >= hi) {
                                break words_loop;
                            }

                            word &= ~(1L << i);

                            action.accept(i);
                        }
                    }
                }

                if (i == Integer.MAX_VALUE && hi == Integer.MAX_VALUE) {
                    action.accept(Integer.MAX_VALUE);
                }
            }

            @Override
            public OfInt trySplit() {
                int hi = getFence();
                int lo = index;
                if (lo < 0) {
                    return null;
                }

                hi = fence = (hi < Integer.MAX_VALUE || !get(Integer.MAX_VALUE))
                        ? previousSetBit(hi - 1) + 1
                        : Integer.MAX_VALUE;

                int mid = (lo + hi) >>> 1;
                if (lo >= mid) {
                    return null;
                }

                index = nextSetBit(mid, wordIndex(hi - 1));
                root = false;

                return new BitSetSpliterator(lo, mid, est >>>= 1, false);
            }

            @Override
            public long estimateSize() {
                getFence();
                return est;
            }

            @Override
            public int characteristics() {
                return (root ? Spliterator.SIZED : 0) |
                    Spliterator.ORDERED | Spliterator.DISTINCT | Spliterator.SORTED;
            }

            @Override
            public Comparator<? super Integer> getComparator() {
                return null;
            }
        }
        return StreamSupport.intStream(new BitSetSpliterator(0, -1, 0, true), false);
    }
    */

}
 
