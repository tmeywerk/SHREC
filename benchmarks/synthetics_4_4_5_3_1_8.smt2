(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun b0 () Bool)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(assert (let ((.def_0 (* (- (/ 303450857826525 562949953421312)) r3))) (let ((.def_1 (* (/ 1352953438395799 4503599627370496) r2))) (let ((.def_2 (* (/ 2642522313431533 4503599627370496) r1))) (let ((.def_3 (* (/ 4357080698521 17592186044416) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 76377640602717 2251799813685248)))) (let ((.def_6 (or b1 b3 .def_5))) (let ((.def_7 (* (/ 796318205418291 2251799813685248) r3))) (let ((.def_8 (* (- (/ 670215101510265 9007199254740992)) r2))) (let ((.def_9 (* (/ 4107540124315627 9007199254740992) r1))) (let ((.def_10 (* (/ 1703755249918839 1125899906842624) r0))) (let ((.def_11 (+ .def_10 .def_9 .def_8 .def_7))) (let ((.def_12 (<= .def_11 (/ 4060309831519811 4503599627370496)))) (let ((.def_13 (not b3))) (let ((.def_14 (or .def_13 b0 .def_12))) (let ((.def_15 (* (/ 1307401240387041 9007199254740992) r3))) (let ((.def_16 (* (/ 3135017291127909 4503599627370496) r2))) (let ((.def_17 (* (/ 1015349249461969 4503599627370496) r1))) (let ((.def_18 (* (/ 4765163043610071 9007199254740992) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (/ 7579226120753375 9007199254740992)))) (let ((.def_21 (or b2 b1 .def_20))) (let ((.def_22 (* (/ 4080539133645535 4503599627370496) r3))) (let ((.def_23 (* (- (/ 7339612020391561 4503599627370496)) r2))) (let ((.def_24 (* (- (/ 3482013352037589 2251799813685248)) r1))) (let ((.def_25 (* (- (/ 3647046180821911 2251799813685248)) r0))) (let ((.def_26 (+ .def_25 .def_24 .def_23 .def_22))) (let ((.def_27 (<= .def_26 (- (/ 1996094658186735 1125899906842624))))) (let ((.def_28 (or b3 b0 .def_27))) (let ((.def_29 (* (- (/ 7925174355532259 9007199254740992)) r3))) (let ((.def_30 (* (- (/ 1734440331570583 1125899906842624)) r2))) (let ((.def_31 (* (/ 7738332274789409 4503599627370496) r1))) (let ((.def_32 (* (- (/ 8704524473024131 9007199254740992)) r0))) (let ((.def_33 (+ .def_32 .def_31 .def_30 .def_29))) (let ((.def_34 (<= .def_33 (- (/ 6244670913828793 9007199254740992))))) (let ((.def_35 (not b2))) (let ((.def_36 (or .def_35 b0 .def_34))) (let ((.def_37 (and .def_36 .def_28 .def_21 .def_14 .def_6))) .def_37)))))))))))))))))))))))))))))))))))))))
(check-sat)
