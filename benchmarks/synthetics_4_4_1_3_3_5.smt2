(set-logic QF_LRA)
(declare-fun r2 () Real)
(declare-fun r0 () Real)
(declare-fun r3 () Real)
(declare-fun r1 () Real)
(assert (let ((.def_0 (* (/ 5148321041564465 9007199254740992) r3))) (let ((.def_1 (* (/ 1762458801427543 562949953421312) r2))) (let ((.def_2 (* (/ 2795708653050019 9007199254740992) r1))) (let ((.def_3 (* (- (/ 3364123847886071 1125899906842624)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 4035429746079877 9007199254740992))))) (let ((.def_6 (* (- (/ 2399114132147359 2251799813685248)) r3))) (let ((.def_7 (* (/ 606893696409921 562949953421312) r2))) (let ((.def_8 (* (/ 8763390916178797 9007199254740992) r1))) (let ((.def_9 (* (/ 7008867141173489 4503599627370496) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 1437964246335339 2251799813685248)))) (let ((.def_12 (* (/ 8028703503738057 2251799813685248) r3))) (let ((.def_13 (* (- (/ 37676222428311 281474976710656)) r2))) (let ((.def_14 (* (- (/ 45396907077805 2251799813685248)) r1))) (let ((.def_15 (* (/ 1820300990351679 9007199254740992) r0))) (let ((.def_16 (+ .def_15 .def_14 .def_13 .def_12))) (let ((.def_17 (<= .def_16 (/ 2542885491437849 4503599627370496)))) (let ((.def_18 (or .def_17 .def_11 .def_5))) .def_18))))))))))))))))))))
(check-sat)
