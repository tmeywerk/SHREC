(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b1 () Bool)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 6562881519004231 4503599627370496) r3))) (let ((.def_1 (* (/ 4818894925657997 4503599627370496) r2))) (let ((.def_2 (* (- (/ 4626924009479 9007199254740992)) r1))) (let ((.def_3 (* (- (/ 1890206544027205 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 1045495273398163 1125899906842624)))) (let ((.def_6 (* (- (/ 8174206228392365 9007199254740992)) r3))) (let ((.def_7 (* (- (/ 4876549638067953 9007199254740992)) r2))) (let ((.def_8 (* (/ 4333821798112467 9007199254740992) r1))) (let ((.def_9 (* (- (/ 2469215902372103 2251799813685248)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 2746887467447667 2251799813685248))))) (let ((.def_12 (or b1 .def_11 .def_5))) (let ((.def_13 (* (- (/ 6307828913691049 9007199254740992)) r3))) (let ((.def_14 (* (/ 5111501450485541 4503599627370496) r2))) (let ((.def_15 (* (/ 5684846063507623 9007199254740992) r1))) (let ((.def_16 (* (- (/ 1125437816885345 1125899906842624)) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (/ 868472182960811 4503599627370496)))) (let ((.def_19 (* (/ 456197624966757 4503599627370496) r3))) (let ((.def_20 (* (- (/ 386900575943639 2251799813685248)) r2))) (let ((.def_21 (* (/ 1463318211581165 1125899906842624) r1))) (let ((.def_22 (* (- (/ 92538385121003 2251799813685248)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (/ 4235078054993195 9007199254740992)))) (let ((.def_25 (or b2 .def_24 .def_18))) (let ((.def_26 (* (/ 131669178862961 9007199254740992) r3))) (let ((.def_27 (* (/ 7440813813528647 4503599627370496) r2))) (let ((.def_28 (* (- (/ 56092806766685 2251799813685248)) r1))) (let ((.def_29 (* (/ 2428203073323857 2251799813685248) r0))) (let ((.def_30 (+ .def_29 .def_28 .def_27 .def_26))) (let ((.def_31 (<= .def_30 (/ 2850347582393943 2251799813685248)))) (let ((.def_32 (* (/ 473497318509039 281474976710656) r3))) (let ((.def_33 (* (/ 3215716047901769 4503599627370496) r2))) (let ((.def_34 (* (- (/ 108814197163791 562949953421312)) r1))) (let ((.def_35 (* (/ 1376569712057373 2251799813685248) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (/ 4407048434864177 4503599627370496)))) (let ((.def_38 (not b3))) (let ((.def_39 (or .def_38 .def_37 .def_31))) (let ((.def_40 (* (/ 6765733695813509 9007199254740992) r3))) (let ((.def_41 (* (/ 1427556277860403 2251799813685248) r2))) (let ((.def_42 (* (/ 5962793387279287 9007199254740992) r1))) (let ((.def_43 (* (- (/ 628891444411157 2251799813685248)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (/ 3675406324215511 4503599627370496)))) (let ((.def_46 (* (- (/ 5339987680992577 9007199254740992)) r3))) (let ((.def_47 (* (/ 3724609851101177 2251799813685248) r2))) (let ((.def_48 (* (- (/ 6418086831697003 4503599627370496)) r1))) (let ((.def_49 (* (/ 374520451785397 140737488355328) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (/ 7883629553568947 9007199254740992)))) (let ((.def_52 (or .def_38 .def_51 .def_45))) (let ((.def_53 (* (- (/ 205642964173817 562949953421312)) r3))) (let ((.def_54 (* (/ 164229363712463 1125899906842624) r2))) (let ((.def_55 (* (/ 4036854529003709 4503599627370496) r1))) (let ((.def_56 (* (/ 277043264294079 1125899906842624) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 1577498107470167 2251799813685248)))) (let ((.def_59 (* (- (/ 5980077504895661 9007199254740992)) r3))) (let ((.def_60 (* (- (/ 9162494396705 2251799813685248)) r2))) (let ((.def_61 (* (/ 106221899061035 140737488355328) r1))) (let ((.def_62 (* (/ 215379518463193 2251799813685248) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 8973901174843 9007199254740992)))) (let ((.def_65 (not b2))) (let ((.def_66 (or .def_65 .def_64 .def_58))) (let ((.def_67 (and .def_66 .def_52 .def_39 .def_25 .def_12))) .def_67)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)