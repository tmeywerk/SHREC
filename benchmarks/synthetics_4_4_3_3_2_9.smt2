(set-logic QF_LRA)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b3 () Bool)
(declare-fun r2 () Real)
(declare-fun b2 () Bool)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (- (/ 7442579592521535 9007199254740992)) r3))) (let ((.def_1 (* (/ 3031254234095919 2251799813685248) r2))) (let ((.def_2 (* (/ 2704954026118635 4503599627370496) r1))) (let ((.def_3 (* (- (/ 293849229095771 562949953421312)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1476860904197711 9007199254740992))))) (let ((.def_6 (* (/ 1144972163806611 1125899906842624) r3))) (let ((.def_7 (* (- (/ 2440660943647821 9007199254740992)) r2))) (let ((.def_8 (* (- (/ 7187891183349019 9007199254740992)) r1))) (let ((.def_9 (* (- (/ 8009978562705175 9007199254740992)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 6998853185704801 9007199254740992))))) (let ((.def_12 (not b2))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 972732309856785 2251799813685248)) r3))) (let ((.def_15 (* (- (/ 22307571705657 70368744177664)) r2))) (let ((.def_16 (* (- (/ 6778424829314477 9007199254740992)) r1))) (let ((.def_17 (* (/ 6253425248626907 2251799813685248) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (/ 166000840306049 562949953421312)))) (let ((.def_20 (* (- (/ 921357745639199 562949953421312)) r3))) (let ((.def_21 (* (/ 1519324766905751 4503599627370496) r2))) (let ((.def_22 (* (/ 5676189939637283 2251799813685248) r1))) (let ((.def_23 (* (/ 6233368451804681 9007199254740992) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 39683145159121 9007199254740992)))) (let ((.def_26 (not b3))) (let ((.def_27 (or .def_26 .def_25 .def_19))) (let ((.def_28 (* (- (/ 700694440354279 562949953421312)) r3))) (let ((.def_29 (* (/ 1468339133123199 2251799813685248) r2))) (let ((.def_30 (* (/ 3409291728659549 9007199254740992) r1))) (let ((.def_31 (* (- (/ 5241090436741493 9007199254740992)) r0))) (let ((.def_32 (+ .def_31 .def_30 .def_29 .def_28))) (let ((.def_33 (<= .def_32 (- (/ 2999987895021189 9007199254740992))))) (let ((.def_34 (* (- (/ 7679453521744725 9007199254740992)) r3))) (let ((.def_35 (* (/ 427943155436603 281474976710656) r2))) (let ((.def_36 (* (- (/ 169588861158581 70368744177664)) r1))) (let ((.def_37 (* (- (/ 1746354554162263 2251799813685248)) r0))) (let ((.def_38 (+ .def_37 .def_36 .def_35 .def_34))) (let ((.def_39 (<= .def_38 (- (/ 3705109707852877 2251799813685248))))) (let ((.def_40 (or .def_26 .def_39 .def_33))) (let ((.def_41 (and .def_40 .def_27 .def_13))) .def_41)))))))))))))))))))))))))))))))))))))))))))
(check-sat)
