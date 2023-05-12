public final class BitwiseAndWithZero {
    /*@ public normal_behavior
      @  ensures \result == 0;
      @  assignable \strictly_nothing;
      @*/
    public static long bitwiseAndWithZero(long a) {
        return a & 0;
    }
}
