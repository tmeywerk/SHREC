(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b1 () Bool)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (- (/ 4994212512494649 4503599627370496)) r3))) (let ((.def_1 (* (/ 27064088706555 4503599627370496) r2))) (let ((.def_2 (* (- (/ 4432443134199141 9007199254740992)) r1))) (let ((.def_3 (* (- (/ 7235435196966785 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 609597091281457 562949953421312))))) (let ((.def_6 (or b3 b2 .def_5))) (let ((.def_7 (* (/ 552158282686459 562949953421312) r3))) (let ((.def_8 (* (/ 1450359944143261 2251799813685248) r2))) (let ((.def_9 (* (- (/ 69147138693415 562949953421312)) r1))) (let ((.def_10 (* (/ 413976214697011 562949953421312) r0))) (let ((.def_11 (+ .def_10 .def_9 .def_8 .def_7))) (let ((.def_12 (<= .def_11 (- (/ 792360771375893 2251799813685248))))) (let ((.def_13 (not b2))) (let ((.def_14 (or b0 .def_13 .def_12))) (let ((.def_15 (* (- (/ 4925267395556067 9007199254740992)) r3))) (let ((.def_16 (* (/ 5865392876568341 9007199254740992) r2))) (let ((.def_17 (* (/ 3048854037011555 4503599627370496) r1))) (let ((.def_18 (* (/ 2820053080815823 4503599627370496) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (/ 1426784918011727 2251799813685248)))) (let ((.def_21 (not b1))) (let ((.def_22 (or .def_21 .def_13 .def_20))) (let ((.def_23 (* (/ 1388519465069067 2251799813685248) r3))) (let ((.def_24 (* (- (/ 451976230336907 1125899906842624)) r2))) (let ((.def_25 (* (/ 1670050512528083 4503599627370496) r1))) (let ((.def_26 (* (- (/ 6192723216275809 9007199254740992)) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (/ 14264352800317 1125899906842624)))) (let ((.def_29 (not b3))) (let ((.def_30 (or .def_29 .def_13 .def_28))) (let ((.def_31 (* (/ 1387578055578963 2251799813685248) r3))) (let ((.def_32 (* (/ 3031579566573245 4503599627370496) r2))) (let ((.def_33 (* (- (/ 1285375162416889 1125899906842624)) r1))) (let ((.def_34 (* (- (/ 1127031424871615 4503599627370496)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 666564919713043 4503599627370496)))) (let ((.def_37 (or b1 b0 .def_36))) (let ((.def_38 (* (- (/ 1380364186360073 562949953421312)) r3))) (let ((.def_39 (* (- (/ 5651003362222045 4503599627370496)) r2))) (let ((.def_40 (* (/ 1212030032858755 1125899906842624) r1))) (let ((.def_41 (* (/ 691970631630995 562949953421312) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (- (/ 20139099051811 70368744177664))))) (let ((.def_44 (or b3 .def_13 .def_43))) (let ((.def_45 (and .def_44 .def_37 .def_30 .def_22 .def_14 .def_6))) .def_45)))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)