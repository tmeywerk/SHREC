(set-logic QF_LRA)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b3 () Bool)
(declare-fun r2 () Real)
(assert (let ((.def_0 (* (- (/ 3131996308091023 4503599627370496)) r3))) (let ((.def_1 (* (- (/ 1818235610442415 4503599627370496)) r2))) (let ((.def_2 (* (/ 3667092110091909 4503599627370496) r1))) (let ((.def_3 (* (- (/ 7016376503194191 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 7838755604725853 4503599627370496))))) (let ((.def_6 (not b3))) (let ((.def_7 (or b2 .def_6 .def_5))) (let ((.def_8 (* (- (/ 6048569543834067 4503599627370496)) r3))) (let ((.def_9 (* (/ 3890906355169351 2251799813685248) r2))) (let ((.def_10 (* (- (/ 8103181466164599 9007199254740992)) r1))) (let ((.def_11 (* (/ 6135890539800221 4503599627370496) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 6585416396400487 9007199254740992))))) (let ((.def_14 (not b2))) (let ((.def_15 (or .def_14 .def_6 .def_13))) (let ((.def_16 (and .def_15 .def_7))) .def_16))))))))))))))))))
(check-sat)
