(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (- (/ 19285672415449 4503599627370496)) r3))) (let ((.def_1 (* (/ 3155452920274877 4503599627370496) r2))) (let ((.def_2 (* (- (/ 4439861341821661 4503599627370496)) r1))) (let ((.def_3 (* (/ 4389099752363643 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 632036444214431 9007199254740992))))) (let ((.def_6 (or b2 b1 .def_5))) (let ((.def_7 (* (/ 4444103576598955 4503599627370496) r3))) (let ((.def_8 (* (/ 2041631288032565 9007199254740992) r2))) (let ((.def_9 (* (- (/ 517195568479893 281474976710656)) r1))) (let ((.def_10 (* (- (/ 1146373263471241 1125899906842624)) r0))) (let ((.def_11 (+ .def_10 .def_9 .def_8 .def_7))) (let ((.def_12 (<= .def_11 (- (/ 2196661450072745 4503599627370496))))) (let ((.def_13 (not b2))) (let ((.def_14 (not b1))) (let ((.def_15 (or .def_14 .def_13 .def_12))) (let ((.def_16 (* (/ 8078329417280215 9007199254740992) r3))) (let ((.def_17 (* (- (/ 1427549068477891 1125899906842624)) r2))) (let ((.def_18 (* (/ 2906543979035759 2251799813685248) r1))) (let ((.def_19 (* (- (/ 3548113600804137 4503599627370496)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (/ 6661664603529 17592186044416)))) (let ((.def_22 (not b0))) (let ((.def_23 (or b1 .def_22 .def_21))) (let ((.def_24 (* (/ 1611555091362363 1125899906842624) r3))) (let ((.def_25 (* (- (/ 4021775119894725 4503599627370496)) r2))) (let ((.def_26 (* (- (/ 182929499541505 4503599627370496)) r1))) (let ((.def_27 (* (- (/ 2971689390415087 9007199254740992)) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (/ 1401559690328959 9007199254740992)))) (let ((.def_30 (or .def_14 b2 .def_29))) (let ((.def_31 (* (/ 287658477571549 4503599627370496) r3))) (let ((.def_32 (* (/ 7046613987772469 2251799813685248) r2))) (let ((.def_33 (* (- (/ 2684453379902623 2251799813685248)) r1))) (let ((.def_34 (* (/ 2236488224406751 9007199254740992) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (/ 1952781140340179 1125899906842624)))) (let ((.def_37 (or b1 b2 .def_36))) (let ((.def_38 (* (/ 133470495580891 140737488355328) r3))) (let ((.def_39 (* (- (/ 2629687744909441 1125899906842624)) r2))) (let ((.def_40 (* (/ 1092836255828917 9007199254740992) r1))) (let ((.def_41 (* (- (/ 6690317871988651 9007199254740992)) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (- (/ 2096605765384535 4503599627370496))))) (let ((.def_44 (or b3 b0 .def_43))) (let ((.def_45 (* (- (/ 2558574331909819 2251799813685248)) r3))) (let ((.def_46 (* (- (/ 6798914805079093 9007199254740992)) r2))) (let ((.def_47 (* (- (/ 282207956080983 281474976710656)) r1))) (let ((.def_48 (* (/ 347064710679189 281474976710656) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (- (/ 455944779373439 1125899906842624))))) (let ((.def_51 (or b3 b2 .def_50))) (let ((.def_52 (and .def_51 .def_44 .def_37 .def_30 .def_23 .def_15 .def_6))) .def_52))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
