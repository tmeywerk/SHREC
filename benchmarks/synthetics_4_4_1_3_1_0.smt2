(set-logic QF_LRA)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(assert (let ((.def_0 (* (- (/ 666730319475959 4503599627370496)) r3))) (let ((.def_1 (* (/ 182825633129645 4503599627370496) r2))) (let ((.def_2 (* (- (/ 752742065530151 2251799813685248)) r1))) (let ((.def_3 (* (/ 3674370436730739 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 461389731449867 2251799813685248))))) (let ((.def_6 (not b1))) (let ((.def_7 (not b2))) (let ((.def_8 (or .def_7 .def_6 .def_5))) .def_8))))))))))
(check-sat)
