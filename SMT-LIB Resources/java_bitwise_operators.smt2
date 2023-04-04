(set-option :produce-models true)
(set-logic ALL)

;====
; SMT-LIB function which mimic Java's bitwise operators AND, OR, and XOR.
;
; To do this, the input numbers must be converted into bitvectors (taking two's
; complement representation into account) so we can use SMT-LIB's built-in
; bitwise operations. We then convert the resulting bitvector back to a number.
;
; All bitvectors here are 64-bit wide because Java's widest primitive is
; `long` and because I don't think it's possible to parameterize bitvector
; sizes. Of course, the below functions will work for other Java integral
; types as well, but will likely be much slower if you only use e.g. 32-bit
; ints.
;
; (Compatibility notes: `bv2int` (or, `bv2nat`) and `int2bv` are not officially
; part of the SMT-LIB standard, but are supported by some SMT solvers. This
; includes the `bvxor` function.)
;====

; Converts a Java integer to a SMT-LIB bitvector
(define-fun jint_to_bv ((x Int)) (_ BitVec 64)
    ((_ int2bv 64) x))

; Converts an SMT-LIB bitvector to a Java int
; representation.
; (Inspired by: https://github.com/ArathaJS/aratha/blob/17f1aca803218fbaf57ec766e6f6ab939bdd2f13/lib/smt2/cvc4/prelude.smt2)
(define-fun bv_to_jint ((x (_ BitVec 64))) Int
    (let ((x_nat (bv2nat x)))
        (ite (>= x_nat 9223372036854775808) ; x_nat >= 2^63
            (- x_nat 18446744073709551616)  ; x_nat - 2^64
            x_nat)))                        ; x_nat

; Java bitwise AND
(define-fun java_bitwise_and ((x Int) (y Int)) Int
    (bv_to_jint (bvand (jint_to_bv x) (jint_to_bv y))))

; Java bitwise OR
(define-fun java_bitwise_or ((x Int) (y Int)) Int
    (bv_to_jint (bvor (jint_to_bv x) (jint_to_bv y))))

; Java bitwise XOR
(define-fun java_bitwise_xor ((x Int) (y Int)) Int
    (bv_to_jint (bvxor (jint_to_bv x) (jint_to_bv y))))

;====
; Tests: SMT-LIB functions
;====

(push)
    (echo "-- Hypothesis: ((x bvand y) bvand z) == (x bvand (y bvand z)) (expected: unsat) --")
    (declare-const bv_x (_ BitVec 64))
    (declare-const bv_y (_ BitVec 64))
    (declare-const bv_z (_ BitVec 64))
    (define-fun conjecture () Bool
        (= (bvand (bvand bv_x bv_y) bv_z) (bvand bv_x (bvand bv_y bv_z))))
    (assert (not conjecture))
    (check-sat)
(pop)

;====
; Tests: Java <-> SMT-LIB conversion
;====

(push)
    (echo "-- Test: bv_to_jint (expected: sat) --")
    (assert (= (bv_to_jint #x0000000000000000) 0))
    (assert (= (bv_to_jint #x0000000000000001) 1))
    (assert (= (bv_to_jint #xffffffffffffffff) (- 1)))
    (assert (= (bv_to_jint #x00000000000000ff) 255))
    (assert (= (bv_to_jint #xffffffffffffff01) (- 255)))
    (assert (= (bv_to_jint #x000000000000002a) 42))
    (assert (= (bv_to_jint #xffffffffffffffd6) (- 42)))
    (assert (= (bv_to_jint #x7fffffffffffffff) 9223372036854775807))
    (assert (= (bv_to_jint #x8000000000000000) (- 9223372036854775808)))
    (check-sat)
(pop)

(push)
    (echo "-- Test: bv_to_jint (expected: sat) --")
    (assert (= (jint_to_bv 0) #x0000000000000000))
    (assert (= (jint_to_bv 1) #x0000000000000001))
    (assert (= (jint_to_bv (- 1)) #xffffffffffffffff))
    (assert (= (jint_to_bv 42) #x000000000000002a))
    (assert (= (jint_to_bv (- 42)) #xffffffffffffffd6))
    (assert (= (jint_to_bv 255) #x00000000000000ff))
    (assert (= (jint_to_bv (- 255)) #xffffffffffffff01))
    (assert (= (jint_to_bv 9223372036854775807) #x7fffffffffffffff))
    (assert (= (jint_to_bv (- 9223372036854775808)) #x8000000000000000))
    (check-sat)
(pop)

(push)
    (echo "-- Test: x == bv_to_jint(jint_to_bv(x)) (for set values of x) (expected: sat) --")
    (assert (= 0 (bv_to_jint (jint_to_bv 0))))
    (assert (= 1 (bv_to_jint (jint_to_bv 1))))
    (assert (= (- 1) (bv_to_jint (jint_to_bv (- 1)))))
    (assert (= 255 (bv_to_jint (jint_to_bv 255))))
    (assert (= (- 255) (bv_to_jint (jint_to_bv (- 255)))))
    (assert (= 42 (bv_to_jint (jint_to_bv 42))))
    (assert (= (- 42) (bv_to_jint (jint_to_bv (- 42)))))
    (assert (= 9223372036854775807 (bv_to_jint (jint_to_bv 9223372036854775807))))
    (assert (= (- 9223372036854775808) (bv_to_jint (jint_to_bv (- 9223372036854775808)))))
    (check-sat)
(pop)

; Verified with Z3 in 1m34s
; Won't finish with CVC5 (>12h)
;(push)
;    (echo "-- Test: x == bv_to_jint(jint_to_bv(x)) (for all x) (expected: unsat) --")
;    (declare-const x Int)
;    (assert (<= (- 9223372036854775808) x))
;    (assert (<= x 9223372036854775807))
;    (define-fun conjecture () Bool
;        (= x (bv_to_jint (jint_to_bv x))))
;    (assert (not conjecture))
;    (check-sat)
;(pop)

;====
; Tests: Bitwise AND
;====

(declare-const x Int)
(assert (<= (- 9223372036854775808) x))
(assert (<= x 9223372036854775807))
(declare-const y Int)
(assert (<= (- 9223372036854775808) y))
(assert (<= y 9223372036854775807))
(declare-const z Int)
(assert (<= (- 9223372036854775808) z))
(assert (<= z 9223372036854775807))

(push)
    (echo "-- Test: java_bitwise_and (expected: sat) --")
    (assert (= (java_bitwise_and 0 0) 0))
    (assert (= (java_bitwise_and 0 42) 0))
    (assert (= (java_bitwise_and 42 0) 0))
    (assert (= (java_bitwise_and 42 42) 42))

    (assert (= (java_bitwise_and 42 13) 8))
    (assert (= (java_bitwise_and 42 (- 13)) 34))
    (assert (= (java_bitwise_and (- 42) 13) 4))
    (assert (= (java_bitwise_and (- 42) (- 13)) (- 46)))
    (check-sat)
(pop)

(push)
    (echo "-- Hypothesis: x & y == y & x (expected: unsat) --")
    (define-fun conjecture () Bool
        (= (java_bitwise_and x y) (java_bitwise_and y x)))
    (assert (not conjecture))
    (check-sat)
(pop)

; Slow test
(push)
    (echo "-- Hypothesis: (x & y) & z == x & (y & z) (expected: unsat) --")
    (define-fun conjecture () Bool
        (= (java_bitwise_and (java_bitwise_and x y) z)
           (java_bitwise_and x (java_bitwise_and y z))))
    (assert (not conjecture))
    (check-sat)
(pop)

; Very slow test (>8h), not verified
;(push)
;    (echo "-- Hypothesis: x & x == x (expected: unsat) --")
;    (define-fun conjecture () Bool
;        (= (java_bitwise_and x x) x))
;    (assert (not conjecture))
;    (check-sat)
;(pop)

(push)
    (echo "-- Hypothesis: x & 0 == 0 (expected: unsat) --")
    (define-fun conjecture () Bool
        (= (java_bitwise_and x 0) 0))
    (assert (not conjecture))
    (check-sat)
(pop)

; Very slow test, not verified
;(push)
;    (echo "-- Hypothesis: x & -1 == x (expected: unsat) --")
;    (define-fun conjecture () Bool
;        (= (java_bitwise_and x (- 1)) x))
;    (assert (not conjecture))
;    (check-sat)
;(pop)

;====
; Tests: Bitwise OR
;====

(push)
    (echo "-- Test: java_bitwise_or (expected: sat) --")
    (assert (= (java_bitwise_or 0 0) 0))
    (assert (= (java_bitwise_or 0 42) 42))
    (assert (= (java_bitwise_or 42 0) 42))
    (assert (= (java_bitwise_or 42 42) 42))

    (assert (= (java_bitwise_or 42 13) 47))
    (assert (= (java_bitwise_or 42 (- 13)) (- 5)))
    (assert (= (java_bitwise_or (- 42) 13) (- 33)))
    (assert (= (java_bitwise_or (- 42) (- 13)) (- 9)))
    (check-sat)
(pop)

;====
; Tests: Bitwise XOR
;====

(push)
    (echo "-- Test: java_bitwise_xor (expected: sat) --")
    (assert (= (java_bitwise_xor 0 0) 0))
    (assert (= (java_bitwise_xor 0 42) 42))
    (assert (= (java_bitwise_xor 42 0) 42))
    (assert (= (java_bitwise_xor 42 42) 0))

    (assert (= (java_bitwise_xor 42 13) 39))
    (assert (= (java_bitwise_xor 42 (- 13)) (- 39)))
    (assert (= (java_bitwise_xor (- 42) 13) (- 37)))
    (assert (= (java_bitwise_xor (- 42) (- 13)) 37))
    (check-sat)
(pop)

(exit)
