(set-logic QF_LRA)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(assert (let ((.def_0 (* (- (/ 399701359789567 281474976710656)) r3))) (let ((.def_1 (* (/ 6684010221862893 9007199254740992) r2))) (let ((.def_2 (* (- (/ 1213283935320927 2251799813685248)) r1))) (let ((.def_3 (* (/ 1138577920381533 2251799813685248) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1236635174784861 1125899906842624))))) (let ((.def_6 (not b2))) (let ((.def_7 (or .def_6 b0 .def_5))) (let ((.def_8 (* (- (/ 5674246597765779 9007199254740992)) r3))) (let ((.def_9 (* (- (/ 1351374314788661 1125899906842624)) r2))) (let ((.def_10 (* (/ 2804354635455299 9007199254740992) r1))) (let ((.def_11 (* (/ 340685113398559 9007199254740992) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 3254375675835353 2251799813685248))))) (let ((.def_14 (or b0 b2 .def_13))) (let ((.def_15 (and .def_14 .def_7))) .def_15)))))))))))))))))
(check-sat)