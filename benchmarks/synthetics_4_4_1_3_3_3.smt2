(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (/ 4027039629121525 9007199254740992) r3))) (let ((.def_1 (* (/ 955257639902819 4503599627370496) r2))) (let ((.def_2 (* (/ 6026862436265553 9007199254740992) r1))) (let ((.def_3 (* (/ 5006604658199625 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 3757613370189071 4503599627370496)))) (let ((.def_6 (* (- (/ 1558019272876883 9007199254740992)) r3))) (let ((.def_7 (* (- (/ 7889870624592481 9007199254740992)) r2))) (let ((.def_8 (* (- (/ 6150086940044301 4503599627370496)) r1))) (let ((.def_9 (* (- (/ 8233744943904737 4503599627370496)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 786379512397559 281474976710656))))) (let ((.def_12 (* (/ 1712187196866459 281474976710656) r3))) (let ((.def_13 (* (/ 808580898240541 2251799813685248) r2))) (let ((.def_14 (* (/ 383980937420097 562949953421312) r1))) (let ((.def_15 (* (- (/ 930369197547417 2251799813685248)) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (/ 785666751708047 562949953421312)))) (let ((.def_18 (or .def_17 .def_11 .def_5))) .def_18))))))))))))))))))))
(check-sat)
