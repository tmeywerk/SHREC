(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (- (/ 1404724046249969 1125899906842624)) r3))) (let ((.def_1 (* (/ 3163835690233757 4503599627370496) r2))) (let ((.def_2 (* (- (/ 2558098329789699 4503599627370496)) r1))) (let ((.def_3 (* (/ 2122296370777959 2251799813685248) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 146158306231295 281474976710656))))) (let ((.def_6 (* (/ 603225264977527 281474976710656) r3))) (let ((.def_7 (* (- (/ 7153487563558627 2251799813685248)) r2))) (let ((.def_8 (* (/ 5783120109640681 4503599627370496) r1))) (let ((.def_9 (* (- (/ 4693646955115031 4503599627370496)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 6234974931129641 4503599627370496))))) (let ((.def_12 (* (- (/ 8721806141864671 9007199254740992)) r3))) (let ((.def_13 (* (- (/ 2955757143042931 2251799813685248)) r2))) (let ((.def_14 (* (- (/ 2920282373247157 2251799813685248)) r1))) (let ((.def_15 (* (- (/ 4248315483897473 9007199254740992)) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (- (/ 46156379749627 17592186044416))))) (let ((.def_18 (or .def_17 .def_11 .def_5))) .def_18))))))))))))))))))))
(check-sat)
