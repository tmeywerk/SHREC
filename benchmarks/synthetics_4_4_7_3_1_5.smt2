(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 1368748569331907 4503599627370496) r3))) (let ((.def_1 (* (/ 2024231025104547 9007199254740992) r2))) (let ((.def_2 (* (/ 6384655125624299 9007199254740992) r1))) (let ((.def_3 (* (- (/ 1234900561923873 562949953421312)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 5567823991797293 9007199254740992))))) (let ((.def_6 (not b2))) (let ((.def_7 (or b0 .def_6 .def_5))) (let ((.def_8 (* (/ 185492654580991 9007199254740992) r3))) (let ((.def_9 (* (- (/ 1248687323388403 1125899906842624)) r2))) (let ((.def_10 (* (- (/ 3628174171974663 9007199254740992)) r1))) (let ((.def_11 (* (/ 1362412202508181 9007199254740992) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (- (/ 5128792221173277 9007199254740992))))) (let ((.def_14 (not b1))) (let ((.def_15 (or .def_6 .def_14 .def_13))) (let ((.def_16 (* (/ 123697554099769 562949953421312) r3))) (let ((.def_17 (* (/ 3032828475680937 4503599627370496) r2))) (let ((.def_18 (* (/ 836387376643149 1125899906842624) r1))) (let ((.def_19 (* (- (/ 5805930110950047 9007199254740992)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (/ 917456832489691 2251799813685248)))) (let ((.def_22 (or .def_14 b0 .def_21))) (let ((.def_23 (* (/ 3969274754229331 4503599627370496) r3))) (let ((.def_24 (* (- (/ 1844969710115231 2251799813685248)) r2))) (let ((.def_25 (* (- (/ 98623766471745 2251799813685248)) r1))) (let ((.def_26 (* (- (/ 95194087343643 140737488355328)) r0))) (let ((.def_27 (+ .def_26 .def_25 .def_24 .def_23))) (let ((.def_28 (<= .def_27 (- (/ 859653915772535 4503599627370496))))) (let ((.def_29 (or b0 .def_14 .def_28))) (let ((.def_30 (* (/ 5373313501398481 9007199254740992) r3))) (let ((.def_31 (* (/ 1365945529197627 4503599627370496) r2))) (let ((.def_32 (* (- (/ 85872262400973 4503599627370496)) r1))) (let ((.def_33 (* (/ 1796931029482493 4503599627370496) r0))) (let ((.def_34 (+ .def_33 .def_32 .def_31 .def_30))) (let ((.def_35 (<= .def_34 (/ 1747672229332503 2251799813685248)))) (let ((.def_36 (or .def_14 b3 .def_35))) (let ((.def_37 (* (- (/ 820594529396201 1125899906842624)) r3))) (let ((.def_38 (* (- (/ 5405229835862841 2251799813685248)) r2))) (let ((.def_39 (* (/ 6286408237933655 9007199254740992) r1))) (let ((.def_40 (* (- (/ 2151636427804743 4503599627370496)) r0))) (let ((.def_41 (+ .def_40 .def_39 .def_38 .def_37))) (let ((.def_42 (<= .def_41 (- (/ 1878749078092525 2251799813685248))))) (let ((.def_43 (or b2 b0 .def_42))) (let ((.def_44 (* (- (/ 2722780490791063 2251799813685248)) r3))) (let ((.def_45 (* (/ 20646181890605 1125899906842624) r2))) (let ((.def_46 (* (- (/ 8715192761150449 9007199254740992)) r1))) (let ((.def_47 (* (/ 637129251839009 2251799813685248) r0))) (let ((.def_48 (+ .def_47 .def_46 .def_45 .def_44))) (let ((.def_49 (<= .def_48 (- (/ 6255297123233179 9007199254740992))))) (let ((.def_50 (not b0))) (let ((.def_51 (or b1 .def_50 .def_49))) (let ((.def_52 (and .def_51 .def_43 .def_36 .def_29 .def_22 .def_15 .def_7))) .def_52))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)