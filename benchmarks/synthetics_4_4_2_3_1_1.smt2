(set-logic QF_LRA)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b3 () Bool)
(declare-fun r2 () Real)
(assert (let ((.def_0 (* (/ 1439013861191693 2251799813685248) r3))) (let ((.def_1 (* (/ 269511191380453 281474976710656) r2))) (let ((.def_2 (* (/ 5394752778037571 9007199254740992) r1))) (let ((.def_3 (* (/ 3218048373403367 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 4140393004166331 9007199254740992)))) (let ((.def_6 (not b2))) (let ((.def_7 (or .def_6 b1 .def_5))) (let ((.def_8 (* (/ 1305517381302729 1125899906842624) r3))) (let ((.def_9 (* (/ 7912399884969303 9007199254740992) r2))) (let ((.def_10 (* (/ 8015494834025479 9007199254740992) r1))) (let ((.def_11 (* (- (/ 384386708505639 4503599627370496)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 2513303882315257 4503599627370496)))) (let ((.def_14 (or b2 b3 .def_13))) (let ((.def_15 (and .def_14 .def_7))) .def_15)))))))))))))))))
(check-sat)
