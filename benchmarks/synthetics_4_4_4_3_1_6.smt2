(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (/ 1342790515186435 1125899906842624) r3))) (let ((.def_1 (* (/ 4077523654867605 9007199254740992) r2))) (let ((.def_2 (* (- (/ 954784878515977 4503599627370496)) r1))) (let ((.def_3 (* (/ 645423013976551 562949953421312) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 4946471696401111 9007199254740992)))) (let ((.def_6 (not b2))) (let ((.def_7 (or .def_6 b1 .def_5))) (let ((.def_8 (* (/ 6297767391378899 2251799813685248) r3))) (let ((.def_9 (* (- (/ 191611108926109 4503599627370496)) r2))) (let ((.def_10 (* (/ 852028177307479 1125899906842624) r1))) (let ((.def_11 (* (- (/ 7731196488633171 4503599627370496)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 2353720856141005 2251799813685248)))) (let ((.def_14 (not b1))) (let ((.def_15 (or .def_14 b2 .def_13))) (let ((.def_16 (* (- (/ 536961842492255 4503599627370496)) r3))) (let ((.def_17 (* (/ 455408723916751 2251799813685248) r2))) (let ((.def_18 (* (- (/ 299555382869703 562949953421312)) r1))) (let ((.def_19 (* (/ 1562556772547555 2251799813685248) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 39466568482173 2251799813685248))))) (let ((.def_22 (not b3))) (let ((.def_23 (or .def_6 .def_22 .def_21))) (let ((.def_24 (* (- (/ 3887585678549743 4503599627370496)) r3))) (let ((.def_25 (* (/ 2838182722177751 2251799813685248) r2))) (let ((.def_26 (* (/ 454662959929229 4503599627370496) r1))) (let ((.def_27 (* (/ 1312127621627581 4503599627370496) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (/ 1675888736733719 4503599627370496)))) (let ((.def_30 (not b0))) (let ((.def_31 (or .def_30 .def_6 .def_29))) (let ((.def_32 (and .def_31 .def_23 .def_15 .def_7))) .def_32))))))))))))))))))))))))))))))))))
(check-sat)
