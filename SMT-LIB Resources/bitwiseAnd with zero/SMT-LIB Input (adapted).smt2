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
(declare-fun u_binaryAnd (U U) U)
(declare-fun u_a () U)
(declare-fun u_heap () U)
(declare-fun k_wellFormed (U) Bool)
(declare-fun k_select (U U U) U)
(declare-fun cast (U T) U)
(declare-fun fieldIdentifier (U) Int)
(declare-const |field_java.lang.Object::<created>| U)
(declare-fun k_null () U)
(declare-fun u_measuredByEmpty () Bool)
(declare-const sort_Field T)
(declare-const sort_java.lang.Object T)
(declare-const sort_Null T)
(declare-const sort_Heap T)
(declare-const sort_any T)
(assert
  (distinct
    sort_int
    sort_Field
    sort_boolean
    sort_java.lang.Object
    sort_Null
    sort_Heap
    sort_any))
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
(assert
  (forall
    ((var_0 U) (var_1 U))
    (!
      (instanceof (u_binaryAnd var_0 var_1) sort_int)
      :pattern
      ((u_binaryAnd var_0 var_1)))))
(assert (instanceof u_a sort_int))
(assert (instanceof u_heap sort_Heap))
(assert
  (forall
    ((x U) (t T))
    (! (subtype (typeof (cast x t)) t) :pattern ((cast x t)))))
(assert
  (forall
    ((x U) (t T))
    (! (=> (subtype (typeof x) t) (= (cast x t) x)) :pattern ((cast x t)))))
(assert (instanceof |field_java.lang.Object::<created>| sort_Field))
(assert (= (fieldIdentifier |field_java.lang.Object::<created>|) (- 2)))
(assert (instanceof k_null sort_Null))
(assert
  (forall
    ((var_x U))
    (!
      (=>
        (instanceof var_x sort_any)
        (=> (= (b2u (instanceof var_x sort_Null)) (b2u true)) (= var_x k_null)))
      :pattern
      ((instanceof var_x sort_Null)))))
(assert
  (forall
    ((var_h U) (var_o U) (var_f U))
    (!
      (=>
        (and
          (instanceof var_h sort_Heap)
          (instanceof var_o sort_java.lang.Object)
          (instanceof var_f sort_Field))
        (=>
          (k_wellFormed var_h)
          (or
            (=
              (cast
                (k_select
                  var_h
                  (cast (k_select var_h var_o var_f) sort_java.lang.Object)
                  |field_java.lang.Object::<created>|)
                sort_boolean)
              (b2u true))
            (= (cast (k_select var_h var_o var_f) sort_java.lang.Object) k_null))))
      :pattern
      ((cast (k_select var_h var_o var_f) sort_java.lang.Object)))))
(assert (subtype sort_Null sort_java.lang.Object))
(assert (subtype sort_int sort_any))
(assert (not (subtype sort_int sort_Field)))
(assert (not (subtype sort_int sort_boolean)))
(assert (not (subtype sort_int sort_java.lang.Object)))
(assert (not (subtype sort_int sort_Heap)))
(assert (subtype sort_Field sort_any))
(assert (not (subtype sort_Field sort_int)))
(assert (not (subtype sort_Field sort_boolean)))
(assert (not (subtype sort_Field sort_java.lang.Object)))
(assert (not (subtype sort_Field sort_Heap)))
(assert (subtype sort_boolean sort_any))
(assert (not (subtype sort_boolean sort_int)))
(assert (not (subtype sort_boolean sort_Field)))
(assert (not (subtype sort_boolean sort_java.lang.Object)))
(assert (not (subtype sort_boolean sort_Heap)))
(assert (subtype sort_java.lang.Object sort_any))
(assert (not (subtype sort_java.lang.Object sort_int)))
(assert (not (subtype sort_java.lang.Object sort_Field)))
(assert (not (subtype sort_java.lang.Object sort_boolean)))
(assert (not (subtype sort_java.lang.Object sort_Heap)))
(assert (subtype sort_Heap sort_any))
(assert (not (subtype sort_Heap sort_int)))
(assert (not (subtype sort_Heap sort_Field)))
(assert (not (subtype sort_Heap sort_boolean)))
(assert (not (subtype sort_Heap sort_java.lang.Object)))
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
(assert (<= (u2i (u_binaryAnd u_a (i2u 0))) 9223372036854775807))
(assert (<= (- 9223372036854775808) (u2i (u_binaryAnd u_a (i2u 0)))))
(assert (k_wellFormed u_heap))
(assert (<= (u2i u_a) 9223372036854775807))
(assert (>= (u2i u_a) (- 9223372036854775808)))
(assert u_measuredByEmpty)
(assert (not (= (u_binaryAnd u_a (i2u 0)) (i2u 0))))
(check-sat)
