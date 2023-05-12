; --- Preamble
; BEGIN preamble from preamble.smt2
(set-option :print-success true)
(set-option :produce-unsat-cores true)
(set-option :produce-models true)
(set-logic ALL)
(declare-sort T 0)
(declare-sort U 0)
(declare-fun instanceof (U T) Bool)
(declare-fun exactinstanceof (U T) Bool)
(declare-fun subtype (T T) Bool)
(declare-fun typeof (U) T)
(assert (forall ((t1 T)) (subtype t1 t1)))
(assert
  (forall
    ((t1 T) (t2 T))
    (!
      (=> (and (subtype t1 t2) (subtype t2 t1)) (= t1 t2))
      :pattern
      ((subtype t1 t2) (subtype t2 t1)))))
(assert
  (forall
    ((t1 T) (t2 T) (t3 T))
    (!
      (=> (and (subtype t1 t2) (subtype t2 t3)) (subtype t1 t3))
      :pattern
      ((subtype t1 t2) (subtype t2 t3)))))
(assert
  (forall
    ((u U) (t T))
    (!
      (= (instanceof u t) (subtype (typeof u) t))
      :pattern
      ((instanceof u t)))))
(assert
  (forall
    ((u U) (t T))
    (!
      (= (exactinstanceof u t) (= (typeof u) t))
      :pattern
      ((exactinstanceof u t)))))
; END preamble from preamble.smt2
; --- Declarations
(declare-fun u2b (U) Bool)
(declare-fun b2u (Bool) U)
(declare-const sort_boolean T)
(declare-fun u2i (U) Int)
(declare-fun i2u (Int) U)
(declare-const sort_int T)
(declare-fun u_a () U)
(declare-fun u_b () U)
(declare-fun u_binaryAnd (U U) U)
(assert (distinct sort_int sort_boolean))
; --- Axioms
(assert (instanceof (b2u true) sort_boolean))
(assert (instanceof (b2u false) sort_boolean))
(assert (forall ((b Bool)) (= (u2b (b2u b)) b)))
; This seems to improve Z3 performance: Needs investigation (probably triggers above)
(assert (not (u2b (b2u false))))
(assert
  (forall
    ((u U))
    (!
      (=>
        (= (typeof u) sort_boolean)
        (or (= u (b2u true)) (= u (b2u false))))
      :pattern
      ((typeof u)))))
(assert
  (forall
    ((x U))
    (!
      (=> (instanceof x sort_boolean) (= (typeof x) sort_boolean))
      :pattern
      ((instanceof x sort_boolean)))))
(assert (forall ((i Int)) (= (u2i (i2u i)) i)))
(assert
  (forall
    ((x U))
    (!
      (=> (= (typeof x) sort_int) (= (i2u (u2i x)) x))
      :pattern
      ((typeof x)))))
(assert
  (forall
    ((t T))
    (!
      (=> (subtype t sort_int) (= t sort_int))
      :pattern
      ((subtype t sort_int)))))
; (assert (forall ((x U)) (! (=> (instanceof x sort_int)  (= (typeof x ) sort_int)) :pattern ((instanceof x sort_int)))))
(assert
  (forall
    ((i Int))
    (! (= (typeof (i2u i)) sort_int) :pattern ((i2u i)))))
(assert (instanceof u_a sort_int))
(assert (instanceof u_b sort_int))
(assert
  (forall
    ((var_0 U) (var_1 U))
    (!
      (instanceof (u_binaryAnd var_0 var_1) sort_int)
      :pattern
      ((u_binaryAnd var_0 var_1)))))
; --- Custom
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

; Function already declared above. Compare below with the explanation of 
; "define-fun" in the SMT-LIB standard (chapter 4.2.3)
(assert (forall ((x U) (y U))
    (= (u_binaryAnd x y)
       (i2u (java_bitwise_and (u2i x) (u2i y))))))

(echo "-- Begin of sequent --")
; --- Sequent
(assert (! (<= (u2i u_a) 9223372036854775807) :named L_0))
(assert (! (>= (u2i u_a) (- 9223372036854775808)) :named L_1))
(assert (! (<= (u2i u_b) 9223372036854775807) :named L_2))
(assert (! (>= (u2i u_b) (- 9223372036854775808)) :named L_3))
(assert
  (!
    (not
      (and
        (>= (u2i (u_binaryAnd u_a u_b)) (- 9223372036854775808))
        (<= (u2i (u_binaryAnd u_a u_b)) 9223372036854775807)))
    :named
    L_4))
(check-sat)
(get-unsat-core) 
