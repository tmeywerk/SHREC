(set-logic QF_LRA)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b0 () Bool)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (- (/ 644353678145285 4503599627370496)) r3))) (let ((.def_1 (* (/ 8307434234758083 9007199254740992) r2))) (let ((.def_2 (* (/ 3757591600075947 1125899906842624) r1))) (let ((.def_3 (* (/ 1884847731036555 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 6469803202789441 4503599627370496)))) (let ((.def_6 (* (/ 299049470310525 9007199254740992) r3))) (let ((.def_7 (* (/ 5581387101005615 4503599627370496) r2))) (let ((.def_8 (* (- (/ 3014446745842819 2251799813685248)) r1))) (let ((.def_9 (* (- (/ 1121322718469083 9007199254740992)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 2142930838313173 4503599627370496))))) (let ((.def_12 (not b0))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 2097607774390049 4503599627370496)) r3))) (let ((.def_15 (* (- (/ 757036297649955 9007199254740992)) r2))) (let ((.def_16 (* (/ 752766028128017 4503599627370496) r1))) (let ((.def_17 (* (/ 277994908732595 2251799813685248) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 7894528955341 35184372088832))))) (let ((.def_20 (* (- (/ 342652769433309 4503599627370496)) r3))) (let ((.def_21 (* (/ 4326298491305797 4503599627370496) r2))) (let ((.def_22 (* (- (/ 419356416812531 4503599627370496)) r1))) (let ((.def_23 (* (- (/ 4819415756255671 9007199254740992)) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (- (/ 270195869996699 2251799813685248))))) (let ((.def_26 (or b0 .def_25 .def_19))) (let ((.def_27 (and .def_26 .def_13))) .def_27)))))))))))))))))))))))))))))
(check-sat)