(set-logic QF_LRA)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(assert (let ((.def_0 (* (/ 3672129924665493 4503599627370496) r3))) (let ((.def_1 (* (/ 443933291021263 562949953421312) r2))) (let ((.def_2 (* (/ 1352666039045835 4503599627370496) r1))) (let ((.def_3 (* (/ 3703865677063669 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 100567135981899 1125899906842624))))) (let ((.def_6 (not b0))) (let ((.def_7 (or .def_6 b3 .def_5))) .def_7)))))))))
(check-sat)
