(set-logic QF_LRA)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b2 () Bool)
(declare-fun r2 () Real)
(assert (let ((.def_0 (* (/ 3684760189246069 9007199254740992) r3))) (let ((.def_1 (* (/ 7053209970389301 9007199254740992) r2))) (let ((.def_2 (* (- (/ 6225522172433403 9007199254740992)) r1))) (let ((.def_3 (* (/ 345631673442229 2251799813685248) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 742168362186085 4503599627370496)))) (let ((.def_6 (not b1))) (let ((.def_7 (not b0))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (* (- (/ 179121709585721 4503599627370496)) r3))) (let ((.def_10 (* (/ 7452305504737555 9007199254740992) r2))) (let ((.def_11 (* (- (/ 722931056013829 1125899906842624)) r1))) (let ((.def_12 (* (/ 861586610056357 1125899906842624) r0))) (let ((.def_13 (+ .def_12 .def_11 .def_10 .def_9))) (let ((.def_14 (<= .def_13 (- (/ 2127972065919027 9007199254740992))))) (let ((.def_15 (or b2 b0 .def_14))) (let ((.def_16 (* (- (/ 1827967507011919 4503599627370496)) r3))) (let ((.def_17 (* (/ 2032998183589521 2251799813685248) r2))) (let ((.def_18 (* (/ 4157240223578495 9007199254740992) r1))) (let ((.def_19 (* (- (/ 7778065819072017 9007199254740992)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 2245542736112793 9007199254740992))))) (let ((.def_22 (or b2 b1 .def_21))) (let ((.def_23 (and .def_22 .def_15 .def_8))) .def_23)))))))))))))))))))))))))
(check-sat)