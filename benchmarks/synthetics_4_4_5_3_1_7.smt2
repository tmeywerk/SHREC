(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b0 () Bool)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(assert (let ((.def_0 (* (- (/ 916752253966841 4503599627370496)) r3))) (let ((.def_1 (* (/ 627766593159903 1125899906842624) r2))) (let ((.def_2 (* (/ 3008051770003221 4503599627370496) r1))) (let ((.def_3 (* (- (/ 1001963641285141 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 170282791741575 4503599627370496)))) (let ((.def_6 (not b3))) (let ((.def_7 (or b1 .def_6 .def_5))) (let ((.def_8 (* (- (/ 2438264932930187 9007199254740992)) r3))) (let ((.def_9 (* (- (/ 7404611734519643 9007199254740992)) r2))) (let ((.def_10 (* (- (/ 597408669347437 4503599627370496)) r1))) (let ((.def_11 (* (/ 428059742974787 1125899906842624) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 3490451271204353 9007199254740992))))) (let ((.def_14 (or b2 .def_6 .def_13))) (let ((.def_15 (* (- (/ 3249594911261511 4503599627370496)) r3))) (let ((.def_16 (* (/ 223168151796069 1125899906842624) r2))) (let ((.def_17 (* (/ 3537702164011565 2251799813685248) r1))) (let ((.def_18 (* (/ 3130273193884761 2251799813685248) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (/ 3868586920238493 4503599627370496)))) (let ((.def_21 (or b1 b0 .def_20))) (let ((.def_22 (* (/ 4948247989199251 9007199254740992) r3))) (let ((.def_23 (* (- (/ 1677355005195499 2251799813685248)) r2))) (let ((.def_24 (* (/ 4215948762584867 2251799813685248) r1))) (let ((.def_25 (* (- (/ 1413364938180221 4503599627370496)) r0))) (let ((.def_26 (+ .def_25 .def_24 .def_23 .def_22))) (let ((.def_27 (<= .def_26 (/ 415295990521473 4503599627370496)))) (let ((.def_28 (not b2))) (let ((.def_29 (or .def_28 b0 .def_27))) (let ((.def_30 (* (/ 2011229187930801 2251799813685248) r3))) (let ((.def_31 (* (- (/ 4434718373967037 4503599627370496)) r2))) (let ((.def_32 (* (/ 3178984261445893 4503599627370496) r1))) (let ((.def_33 (* (- (/ 4135589848363685 4503599627370496)) r0))) (let ((.def_34 (+ .def_33 .def_32 .def_31 .def_30))) (let ((.def_35 (<= .def_34 (- (/ 18751571245459 1125899906842624))))) (let ((.def_36 (or b0 .def_28 .def_35))) (let ((.def_37 (and .def_36 .def_29 .def_21 .def_14 .def_7))) .def_37)))))))))))))))))))))))))))))))))))))))
(check-sat)
