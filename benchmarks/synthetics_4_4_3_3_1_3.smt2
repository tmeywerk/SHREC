(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(assert (let ((.def_0 (* (- (/ 4798915329207801 4503599627370496)) r3))) (let ((.def_1 (* (- (/ 1782895990445165 2251799813685248)) r2))) (let ((.def_2 (* (/ 953200578797757 562949953421312) r1))) (let ((.def_3 (* (/ 353916444945509 562949953421312) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 5439873609551397 9007199254740992))))) (let ((.def_6 (not b0))) (let ((.def_7 (not b2))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (* (- (/ 69081416659975 1125899906842624)) r3))) (let ((.def_10 (* (/ 693625046616911 1125899906842624) r2))) (let ((.def_11 (* (/ 253546129045863 1125899906842624) r1))) (let ((.def_12 (* (- (/ 1141826531761213 4503599627370496)) r0))) (let ((.def_13 (+ .def_12 .def_11 .def_10 .def_9))) (let ((.def_14 (<= .def_13 (- (/ 25896384526731 281474976710656))))) (let ((.def_15 (not b1))) (let ((.def_16 (or b2 .def_15 .def_14))) (let ((.def_17 (* (/ 791272440073573 562949953421312) r3))) (let ((.def_18 (* (- (/ 2377249526465705 4503599627370496)) r2))) (let ((.def_19 (* (/ 8813904593166281 9007199254740992) r1))) (let ((.def_20 (* (/ 1969319693106753 4503599627370496) r0))) (let ((.def_21 (+ .def_20 .def_19 .def_18 .def_17))) (let ((.def_22 (<= .def_21 (/ 3701225397719611 4503599627370496)))) (let ((.def_23 (or b3 .def_15 .def_22))) (let ((.def_24 (and .def_23 .def_16 .def_8))) .def_24))))))))))))))))))))))))))
(check-sat)
