(set-logic QF_LRA)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b2 () Bool)
(declare-fun r2 () Real)
(declare-fun b0 () Bool)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 1854588458164817 2251799813685248) r3))) (let ((.def_1 (* (- (/ 3335201679349901 2251799813685248)) r2))) (let ((.def_2 (* (- (/ 3994362500875605 4503599627370496)) r1))) (let ((.def_3 (* (/ 803469440340759 1125899906842624) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 590375042171991 562949953421312))))) (let ((.def_6 (* (/ 8896200145315689 9007199254740992) r3))) (let ((.def_7 (* (/ 6884643024734269 9007199254740992) r2))) (let ((.def_8 (* (- (/ 1841835763376361 4503599627370496)) r1))) (let ((.def_9 (* (/ 3664042485107455 4503599627370496) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 320449075279751 562949953421312)))) (let ((.def_12 (not b2))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 494736681574477 1125899906842624)) r3))) (let ((.def_15 (* (/ 437581946827745 2251799813685248) r2))) (let ((.def_16 (* (/ 2634146496992935 4503599627370496) r1))) (let ((.def_17 (* (- (/ 3383444993851443 4503599627370496)) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 1956718077527033 4503599627370496))))) (let ((.def_20 (* (/ 1591596263064393 2251799813685248) r3))) (let ((.def_21 (* (/ 125078380732641 9007199254740992) r2))) (let ((.def_22 (* (- (/ 3610978352623867 2251799813685248)) r1))) (let ((.def_23 (* (/ 2857374164429227 1125899906842624) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 253887332399819 1125899906842624)))) (let ((.def_26 (or b0 .def_25 .def_19))) (let ((.def_27 (and .def_26 .def_13))) .def_27)))))))))))))))))))))))))))))
(check-sat)