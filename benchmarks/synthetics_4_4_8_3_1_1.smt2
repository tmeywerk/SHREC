(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (/ 2141234147475459 4503599627370496) r3))) (let ((.def_1 (* (- (/ 3559153695561353 2251799813685248)) r2))) (let ((.def_2 (* (- (/ 34278403894569 9007199254740992)) r1))) (let ((.def_3 (* (- (/ 599931882234911 562949953421312)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 690285749151501 562949953421312))))) (let ((.def_6 (not b1))) (let ((.def_7 (or b2 .def_6 .def_5))) (let ((.def_8 (* (- (/ 505351112318923 9007199254740992)) r3))) (let ((.def_9 (* (- (/ 614919206417321 562949953421312)) r2))) (let ((.def_10 (* (- (/ 7381121783354951 9007199254740992)) r1))) (let ((.def_11 (* (/ 3539034290047199 4503599627370496) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 181959117921791 562949953421312))))) (let ((.def_14 (not b3))) (let ((.def_15 (or b2 .def_14 .def_13))) (let ((.def_16 (* (- (/ 4731175660156177 2251799813685248)) r3))) (let ((.def_17 (* (- (/ 3700580430773663 4503599627370496)) r2))) (let ((.def_18 (* (- (/ 4678805224116465 4503599627370496)) r1))) (let ((.def_19 (* (- (/ 1248336723957589 4503599627370496)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 5061173865784327 2251799813685248))))) (let ((.def_22 (or b3 b1 .def_21))) (let ((.def_23 (* (/ 597306861757083 1125899906842624) r3))) (let ((.def_24 (* (- (/ 417342166742167 281474976710656)) r2))) (let ((.def_25 (* (/ 8158650246094109 9007199254740992) r1))) (let ((.def_26 (* (- (/ 668061480113041 1125899906842624)) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (- (/ 799310192109137 4503599627370496))))) (let ((.def_29 (not b0))) (let ((.def_30 (or b1 .def_29 .def_28))) (let ((.def_31 (* (- (/ 1471300871683347 1125899906842624)) r3))) (let ((.def_32 (* (- (/ 708706164441809 1125899906842624)) r2))) (let ((.def_33 (* (/ 1845688053392013 2251799813685248) r1))) (let ((.def_34 (* (/ 1581291980924487 1125899906842624) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 3645776061159913 9007199254740992)))) (let ((.def_37 (or b2 .def_29 .def_36))) (let ((.def_38 (* (/ 6854863893941085 4503599627370496) r3))) (let ((.def_39 (* (- (/ 4169316597692071 9007199254740992)) r2))) (let ((.def_40 (* (/ 3904439996567235 2251799813685248) r1))) (let ((.def_41 (* (/ 1128357968059717 9007199254740992) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (/ 6551881791836061 4503599627370496)))) (let ((.def_44 (or b2 b3 .def_43))) (let ((.def_45 (* (/ 1163579382794671 2251799813685248) r3))) (let ((.def_46 (* (/ 37994774677505 70368744177664) r2))) (let ((.def_47 (* (- (/ 3679235222951 1125899906842624)) r1))) (let ((.def_48 (* (- (/ 61524290179193 2251799813685248)) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 5852715365638413 9007199254740992)))) (let ((.def_51 (or b2 b3 .def_50))) (let ((.def_52 (* (- (/ 4053437817035609 9007199254740992)) r3))) (let ((.def_53 (* (- (/ 3947684543060301 9007199254740992)) r2))) (let ((.def_54 (* (- (/ 6238402677483535 9007199254740992)) r1))) (let ((.def_55 (* (/ 632513245697211 562949953421312) r0))) (let ((.def_56 (+ .def_55 .def_54 .def_53 .def_52))) (let ((.def_57 (<= .def_56 (/ 128471881273143 2251799813685248)))) (let ((.def_58 (or b0 b3 .def_57))) (let ((.def_59 (and .def_58 .def_51 .def_44 .def_37 .def_30 .def_22 .def_15 .def_7))) .def_59)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)