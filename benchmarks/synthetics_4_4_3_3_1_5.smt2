(set-logic QF_LRA)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(assert (let ((.def_0 (* (- (/ 216171404069257 2251799813685248)) r3))) (let ((.def_1 (* (/ 8691644530460417 9007199254740992) r2))) (let ((.def_2 (* (- (/ 1253889250754821 1125899906842624)) r1))) (let ((.def_3 (* (/ 8597574304146559 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 145481283015457 4503599627370496))))) (let ((.def_6 (not b0))) (let ((.def_7 (or b3 .def_6 .def_5))) (let ((.def_8 (* (/ 4316142258896751 4503599627370496) r3))) (let ((.def_9 (* (- (/ 6163615462106383 9007199254740992)) r2))) (let ((.def_10 (* (/ 6279700628056495 9007199254740992) r1))) (let ((.def_11 (* (/ 199180957632725 2251799813685248) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 3367904959842727 9007199254740992)))) (let ((.def_14 (not b3))) (let ((.def_15 (not b1))) (let ((.def_16 (or .def_15 .def_14 .def_13))) (let ((.def_17 (* (- (/ 162491509000929 562949953421312)) r3))) (let ((.def_18 (* (- (/ 2516373493609829 9007199254740992)) r2))) (let ((.def_19 (* (/ 4029707460078731 4503599627370496) r1))) (let ((.def_20 (* (/ 5600830561431323 9007199254740992) r0))) (let ((.def_21 (+ .def_20 .def_19 .def_18 .def_17))) (let ((.def_22 (<= .def_21 (/ 3377568173912319 9007199254740992)))) (let ((.def_23 (or b0 b3 .def_22))) (let ((.def_24 (and .def_23 .def_16 .def_7))) .def_24))))))))))))))))))))))))))
(check-sat)
