(set-logic QF_LRA)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(assert (let ((.def_0 (* (/ 647534915163105 1125899906842624) r3))) (let ((.def_1 (* (/ 2376486637827065 4503599627370496) r2))) (let ((.def_2 (* (/ 1709826701919995 2251799813685248) r1))) (let ((.def_3 (* (- (/ 1788749556716227 2251799813685248)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 648991111913427 1125899906842624)))) (let ((.def_6 (not b0))) (let ((.def_7 (not b1))) (let ((.def_8 (or .def_7 .def_6 .def_5))) .def_8))))))))))
(check-sat)
