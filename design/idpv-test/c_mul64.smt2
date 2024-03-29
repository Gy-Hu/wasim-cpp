; SMT 2
(set-info :source "Generated by CBMC 5.95.1 (cbmc-5.95.1)")
(set-option :produce-models true)
(set-logic QF_AUFBV)

; find_symbols
(declare-fun |goto_symex::&92;guard#1| () Bool)
; convert
; Converting var_no 0 with expr ID of symbol
(define-fun B0 () Bool |goto_symex::&92;guard#1|)

; convert
; Converting var_no 1 with expr ID of symbol
(define-fun B1 () Bool |goto_symex::&92;guard#1|)

; convert
; Converting var_no 2 with expr ID of not
(define-fun B2 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 3 with expr ID of not
(define-fun B3 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 4 with expr ID of not
(define-fun B4 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 5 with expr ID of not
(define-fun B5 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 6 with expr ID of not
(define-fun B6 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 7 with expr ID of not
(define-fun B7 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 8 with expr ID of not
(define-fun B8 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 9 with expr ID of not
(define-fun B9 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 10 with expr ID of not
(define-fun B10 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 11 with expr ID of not
(define-fun B11 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 12 with expr ID of not
(define-fun B12 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 13 with expr ID of not
(define-fun B13 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 14 with expr ID of not
(define-fun B14 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 15 with expr ID of not
(define-fun B15 () Bool (not |goto_symex::&92;guard#1|))

; find_symbols
(declare-fun |goto_symex::&92;guard#2| () Bool)
; convert
; Converting var_no 16 with expr ID of and
(define-fun B16 () Bool (and (not |goto_symex::&92;guard#1|) |goto_symex::&92;guard#2|))

; convert
; Converting var_no 17 with expr ID of not
(define-fun B17 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 18 with expr ID of not
(define-fun B18 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 19 with expr ID of not
(define-fun B19 () Bool (not |goto_symex::&92;guard#1|))

; convert
; Converting var_no 20 with expr ID of not
(define-fun B20 () Bool (not |goto_symex::&92;guard#1|))

; set_to true (equal)
(define-fun |__CPROVER_dead_object#1| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |__CPROVER_deallocated#1| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |__CPROVER_memory_leak#1| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |__CPROVER_rounding_mode#1| () (_ BitVec 32) (_ bv0 32))

; set_to true (equal)
(define-fun |__CPROVER::constant_infinity_uint#1| () (_ BitVec 32) (_ bv0 32))

; find_symbols
(declare-fun |main::1::a!0@1#1| () (_ BitVec 64))
; set_to true (equal)
(define-fun |__muldf3(double,double)::a!0@1#1| () (_ BitVec 64) |main::1::a!0@1#1|)

; find_symbols
(declare-fun |main::1::b!0@1#1| () (_ BitVec 64))
; set_to true (equal)
(define-fun |__muldf3(double,double)::b!0@1#1| () (_ BitVec 64) |main::1::b!0@1#1|)

; this is a model for typecast : f64_52 -> B64
(define-fun float_bv.typecast_f64_52->B64 ((op0 (_ BitVec 64))) (_ BitVec 64) ((_ extract 63 0) op0))
; set_to true (equal)
(define-fun |__muldf3(double,double)::1::af!0@1#2| () (_ BitVec 64) ((_ extract 63 0) |__muldf3(double,double)::a!0@1#1|))

; set_to true (equal)
(define-fun |__muldf3(double,double)::1::af!0@1#2..anon-double_cast::f| () (_ BitVec 64) |__muldf3(double,double)::a!0@1#1|)

; set_to true (equal)
(define-fun |__muldf3(double,double)::1::af!0@1#2..anon-double_cast::i| () (_ BitVec 64) ((_ extract 63 0) |__muldf3(double,double)::a!0@1#1|))

; set_to true (equal)
(define-fun |__muldf3(double,double)::1::bf!0@1#2| () (_ BitVec 64) ((_ extract 63 0) |__muldf3(double,double)::b!0@1#1|))

; set_to true (equal)
(define-fun |__muldf3(double,double)::1::bf!0@1#2..anon-double_cast::f| () (_ BitVec 64) |__muldf3(double,double)::b!0@1#1|)

; set_to true (equal)
(define-fun |__muldf3(double,double)::1::bf!0@1#2..anon-double_cast::i| () (_ BitVec 64) ((_ extract 63 0) |__muldf3(double,double)::b!0@1#1|))

; set_to true (equal)
(define-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::a1!0@1#1| () (_ BitVec 64) |__muldf3(double,double)::1::af!0@1#2..anon-double_cast::i|)

; set_to true (equal)
(define-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::a2!0@1#1| () (_ BitVec 64) |__muldf3(double,double)::1::bf!0@1#2..anon-double_cast::i|)

; set_to true (equal)
(define-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::sign!0@1#2| () (_ BitVec 64) (bvxor (bvand |muldf3_classical(unsigned_long_int,unsigned_long_int)::a1!0@1#1| (_ bv9223372036854775808 64)) (bvand |muldf3_classical(unsigned_long_int,unsigned_long_int)::a2!0@1#1| (_ bv9223372036854775808 64))))

; set_to true (equal)
(define-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp1!0@1#2| () (_ BitVec 64) (bvlshr (bvand |muldf3_classical(unsigned_long_int,unsigned_long_int)::a1!0@1#1| (_ bv9218868437227405312 64)) ((_ zero_extend 32) (_ bv52 32))))

; set_to true (equal)
(define-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp2!0@1#2| () (_ BitVec 64) (bvlshr (bvand |muldf3_classical(unsigned_long_int,unsigned_long_int)::a2!0@1#1| (_ bv9218868437227405312 64)) ((_ zero_extend 32) (_ bv52 32))))

; set_to true (equal)
(define-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant1!0@1#2| () (_ BitVec 64) (bvor (bvand |muldf3_classical(unsigned_long_int,unsigned_long_int)::a1!0@1#1| (_ bv4503599627370495 64)) (_ bv4503599627370496 64)))

; set_to true (equal)
(define-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant2!0@1#2| () (_ BitVec 64) (bvor (bvand |muldf3_classical(unsigned_long_int,unsigned_long_int)::a2!0@1#1| (_ bv4503599627370495 64)) (_ bv4503599627370496 64)))

; set_to true
(assert (= |goto_symex::&92;guard#1| (not (and (not (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::a1!0@1#1| (_ bv0 64))) (not (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::a2!0@1#1| (_ bv0 64)))))))

; set_to true (equal)
(define-fun |goto_symex::return_value::muldf3_classical(unsigned_long_int,unsigned_long_int)!0#1| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp!0@1#2| () (_ BitVec 64) (bvadd (bvadd |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp1!0@1#2| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp2!0@1#2|) (_ bv18446744073709550593 64)))

; set_to true (equal)
(define-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::a1!0@1#1| () (_ BitVec 64) |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant1!0@1#2|)

; set_to true (equal)
(define-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::a2!0@1#1| () (_ BitVec 64) |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant2!0@1#2|)

; set_to true (equal)
(define-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#2| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::1::bit!0@1#2| () (_ BitVec 32) (_ bv0 32))

; set_to true
(assert (= |goto_symex::&92;guard#2| (not (= (bvand |doubleMulParts(unsigned_long_int,unsigned_long_int)::a1!0@1#1| (_ bv1 64)) (_ bv0 64)))))

; set_to true (equal)
(define-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#3| () (_ BitVec 64) |doubleMulParts(unsigned_long_int,unsigned_long_int)::a2!0@1#1|)

; set_to true (equal)
(define-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#4| () (_ BitVec 64) (ite (and (not |goto_symex::&92;guard#1|) (not |goto_symex::&92;guard#2|)) (_ bv0 64) |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#3|))

; set_to true (equal)
(define-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::1::bit!0@1#3| () (_ BitVec 32) (_ bv1 32))

; set_to true (equal)
(define-fun |__muldf3(double,double)::$tmp::return_value_muldf3_classical!0@1#2| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |__muldf3(double,double)::1::cf!0@1#2| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |__muldf3(double,double)::1::cf!0@1#2..anon-double_cast::f| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |__muldf3(double,double)::1::cf!0@1#2..anon-double_cast::i| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |goto_symex::return_value::__muldf3(double,double)!0#1| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |main::$tmp::return_value___muldf3!0@1#2| () (_ BitVec 64) (_ bv0 64))

; set_to true (equal)
(define-fun |main::1::result!0@1#2| () (_ BitVec 64) (_ bv0 64))

; convert
; Converting var_no 21 with expr ID of =
(define-fun B21 () Bool (= |main::1::a!0@1#1| |main::1::a!0@1#1|))

; convert
; Converting var_no 22 with expr ID of =
(define-fun B22 () Bool (= |main::1::a!0@1#1| |main::1::a!0@1#1|))

; convert
; Converting var_no 23 with expr ID of =
(define-fun B23 () Bool (= |main::1::b!0@1#1| |main::1::b!0@1#1|))

; convert
; Converting var_no 24 with expr ID of =
(define-fun B24 () Bool (= |main::1::b!0@1#1| |main::1::b!0@1#1|))

; find_symbols
(declare-fun |main::1::result!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 25 with expr ID of =
(define-fun B25 () Bool (= |main::1::result!0@1#1| |main::1::result!0@1#1|))

; convert
; Converting var_no 26 with expr ID of =
(define-fun B26 () Bool (= |main::1::result!0@1#1| |main::1::result!0@1#1|))

; find_symbols
(declare-fun |main::$tmp::return_value___muldf3!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 27 with expr ID of =
(define-fun B27 () Bool (= |main::$tmp::return_value___muldf3!0@1#1| |main::$tmp::return_value___muldf3!0@1#1|))

; convert
; Converting var_no 28 with expr ID of =
(define-fun B28 () Bool (= |main::$tmp::return_value___muldf3!0@1#1| |main::$tmp::return_value___muldf3!0@1#1|))

; find_symbols
(declare-fun |__muldf3(double,double)::1::af!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 29 with expr ID of =
(define-fun B29 () Bool (= |__muldf3(double,double)::1::af!0@1#1| |__muldf3(double,double)::1::af!0@1#1|))

; convert
; Converting var_no 30 with expr ID of =
(define-fun B30 () Bool (= |__muldf3(double,double)::1::af!0@1#1| |__muldf3(double,double)::1::af!0@1#1|))

; find_symbols
(declare-fun |__muldf3(double,double)::1::bf!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 31 with expr ID of =
(define-fun B31 () Bool (= |__muldf3(double,double)::1::bf!0@1#1| |__muldf3(double,double)::1::bf!0@1#1|))

; convert
; Converting var_no 32 with expr ID of =
(define-fun B32 () Bool (= |__muldf3(double,double)::1::bf!0@1#1| |__muldf3(double,double)::1::bf!0@1#1|))

; find_symbols
(declare-fun |__muldf3(double,double)::1::cf!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 33 with expr ID of =
(define-fun B33 () Bool (= |__muldf3(double,double)::1::cf!0@1#1| |__muldf3(double,double)::1::cf!0@1#1|))

; convert
; Converting var_no 34 with expr ID of =
(define-fun B34 () Bool (= |__muldf3(double,double)::1::cf!0@1#1| |__muldf3(double,double)::1::cf!0@1#1|))

; find_symbols
(declare-fun |__muldf3(double,double)::$tmp::return_value_muldf3_classical!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 35 with expr ID of =
(define-fun B35 () Bool (= |__muldf3(double,double)::$tmp::return_value_muldf3_classical!0@1#1| |__muldf3(double,double)::$tmp::return_value_muldf3_classical!0@1#1|))

; convert
; Converting var_no 36 with expr ID of =
(define-fun B36 () Bool (= |__muldf3(double,double)::$tmp::return_value_muldf3_classical!0@1#1| |__muldf3(double,double)::$tmp::return_value_muldf3_classical!0@1#1|))

; find_symbols
(declare-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::sign!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 37 with expr ID of =
(define-fun B37 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::sign!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::sign!0@1#1|))

; convert
; Converting var_no 38 with expr ID of =
(define-fun B38 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::sign!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::sign!0@1#1|))

; find_symbols
(declare-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp1!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 39 with expr ID of =
(define-fun B39 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp1!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp1!0@1#1|))

; convert
; Converting var_no 40 with expr ID of =
(define-fun B40 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp1!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp1!0@1#1|))

; find_symbols
(declare-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp2!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 41 with expr ID of =
(define-fun B41 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp2!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp2!0@1#1|))

; convert
; Converting var_no 42 with expr ID of =
(define-fun B42 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp2!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp2!0@1#1|))

; find_symbols
(declare-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant1!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 43 with expr ID of =
(define-fun B43 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant1!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant1!0@1#1|))

; convert
; Converting var_no 44 with expr ID of =
(define-fun B44 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant1!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant1!0@1#1|))

; find_symbols
(declare-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant2!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 45 with expr ID of =
(define-fun B45 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant2!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant2!0@1#1|))

; convert
; Converting var_no 46 with expr ID of =
(define-fun B46 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant2!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant2!0@1#1|))

; find_symbols
(declare-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 47 with expr ID of =
(define-fun B47 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp!0@1#1|))

; convert
; Converting var_no 48 with expr ID of =
(define-fun B48 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::exp!0@1#1|))

; find_symbols
(declare-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::result!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 49 with expr ID of =
(define-fun B49 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::result!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::result!0@1#1|))

; convert
; Converting var_no 50 with expr ID of =
(define-fun B50 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::result!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::result!0@1#1|))

; find_symbols
(declare-fun |muldf3_classical(unsigned_long_int,unsigned_long_int)::$tmp::return_value_doubleMulParts!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 51 with expr ID of =
(define-fun B51 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::$tmp::return_value_doubleMulParts!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::$tmp::return_value_doubleMulParts!0@1#1|))

; convert
; Converting var_no 52 with expr ID of =
(define-fun B52 () Bool (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::$tmp::return_value_doubleMulParts!0@1#1| |muldf3_classical(unsigned_long_int,unsigned_long_int)::$tmp::return_value_doubleMulParts!0@1#1|))

; find_symbols
(declare-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#1| () (_ BitVec 64))
; convert
; Converting var_no 53 with expr ID of =
(define-fun B53 () Bool (= |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#1| |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#1|))

; convert
; Converting var_no 54 with expr ID of =
(define-fun B54 () Bool (= |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#1| |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::total!0@1#1|))

; find_symbols
(declare-fun |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::1::bit!0@1#1| () (_ BitVec 32))
; convert
; Converting var_no 55 with expr ID of =
(define-fun B55 () Bool (= |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::1::bit!0@1#1| |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::1::bit!0@1#1|))

; convert
; Converting var_no 56 with expr ID of =
(define-fun B56 () Bool (= |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::1::bit!0@1#1| |doubleMulParts(unsigned_long_int,unsigned_long_int)::1::1::bit!0@1#1|))

; convert
; Converting var_no 57 with expr ID of symbol
(define-fun B57 () Bool |goto_symex::&92;guard#1|)

; convert
; Converting var_no 58 with expr ID of and
(define-fun B58 () Bool (and (not (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::a1!0@1#1| (_ bv0 64))) (not (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::a2!0@1#1| (_ bv0 64)))))

; convert
; Converting var_no 59 with expr ID of =
(define-fun B59 () Bool (= (bvand |doubleMulParts(unsigned_long_int,unsigned_long_int)::a1!0@1#1| (_ bv1 64)) (_ bv0 64)))

; find_symbols
(declare-fun |symex::args::0| () (_ BitVec 64))
; set_to true
(assert (= |main::1::a!0@1#1| |symex::args::0|))

; find_symbols
(declare-fun |symex::args::1| () (_ BitVec 64))
; set_to true
(assert (= |main::1::b!0@1#1| |symex::args::1|))

; find_symbols
(declare-fun |symex::args::2| () (_ BitVec 64))
; set_to true
(assert (= |__muldf3(double,double)::1::af!0@1#2..anon-double_cast::i| |symex::args::2|))

; find_symbols
(declare-fun |symex::args::3| () (_ BitVec 64))
; set_to true
(assert (= |__muldf3(double,double)::1::bf!0@1#2..anon-double_cast::i| |symex::args::3|))

; find_symbols
(declare-fun |symex::args::4| () (_ BitVec 64))
; set_to true
(assert (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant1!0@1#2| |symex::args::4|))

; find_symbols
(declare-fun |symex::args::5| () (_ BitVec 64))
; set_to true
(assert (= |muldf3_classical(unsigned_long_int,unsigned_long_int)::1::mant2!0@1#2| |symex::args::5|))

; set_to true
(assert B57)

; set_to false
(assert (not false))

; convert
; Converting var_no 60 with expr ID of not
(define-fun B60 () Bool (not false))

; set_to true
(assert B60)




(exit)
; end of SMT2 file