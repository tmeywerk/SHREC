(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (/ 1348210084466049 4503599627370496) r3))) (let ((.def_1 (* (- (/ 354011153316261 562949953421312)) r2))) (let ((.def_2 (* (/ 1424656251452987 1125899906842624) r1))) (let ((.def_3 (* (- (/ 7331458819363509 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 88473657210139 4503599627370496))))) (let ((.def_6 (not b2))) (let ((.def_7 (not b0))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (* (- (/ 1549608128716305 1125899906842624)) r3))) (let ((.def_10 (* (- (/ 1135470675970199 1125899906842624)) r2))) (let ((.def_11 (* (- (/ 1408151816463041 1125899906842624)) r1))) (let ((.def_12 (* (/ 44144089116069 140737488355328) r0))) (let ((.def_13 (+ .def_12 .def_11 .def_10 .def_9))) (let ((.def_14 (<= .def_13 (- (/ 3343310281533749 2251799813685248))))) (let ((.def_15 (not b1))) (let ((.def_16 (or .def_15 .def_7 .def_14))) (let ((.def_17 (* (/ 8319725452671845 9007199254740992) r3))) (let ((.def_18 (* (- (/ 1915650569320831 4503599627370496)) r2))) (let ((.def_19 (* (- (/ 278885200798463 4503599627370496)) r1))) (let ((.def_20 (* (/ 6580396597825569 9007199254740992) r0))) (let ((.def_21 (+ .def_20 .def_19 .def_18 .def_17))) (let ((.def_22 (<= .def_21 (/ 990271159902179 1125899906842624)))) (let ((.def_23 (not b3))) (let ((.def_24 (or b2 .def_23 .def_22))) (let ((.def_25 (* (- (/ 137105589834487 140737488355328)) r3))) (let ((.def_26 (* (- (/ 1869737281277885 9007199254740992)) r2))) (let ((.def_27 (* (/ 6683315880038503 4503599627370496) r1))) (let ((.def_28 (* (/ 2853038951880749 4503599627370496) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (/ 3336074024154167 4503599627370496)))) (let ((.def_31 (or .def_7 b3 .def_30))) (let ((.def_32 (* (- (/ 1121691580771137 2251799813685248)) r3))) (let ((.def_33 (* (/ 438518966767419 2251799813685248) r2))) (let ((.def_34 (* (/ 224459590588141 1125899906842624) r1))) (let ((.def_35 (* (/ 418168892884413 1125899906842624) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (/ 744138698092875 2251799813685248)))) (let ((.def_38 (or .def_23 b1 .def_37))) (let ((.def_39 (* (/ 5059745745741685 9007199254740992) r3))) (let ((.def_40 (* (- (/ 3251453143964621 2251799813685248)) r2))) (let ((.def_41 (* (- (/ 2585956638735331 1125899906842624)) r1))) (let ((.def_42 (* (/ 2838667639676779 2251799813685248) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (- (/ 4653706166887493 9007199254740992))))) (let ((.def_45 (or .def_6 b3 .def_44))) (let ((.def_46 (* (/ 2257959580078161 1125899906842624) r3))) (let ((.def_47 (* (/ 175004864937559 4503599627370496) r2))) (let ((.def_48 (* (- (/ 1362365407010053 1125899906842624)) r1))) (let ((.def_49 (* (- (/ 683818728656165 562949953421312)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (/ 3811222344569155 9007199254740992)))) (let ((.def_52 (or b3 b2 .def_51))) (let ((.def_53 (* (- (/ 482886534279727 1125899906842624)) r3))) (let ((.def_54 (* (/ 324353386083407 2251799813685248) r2))) (let ((.def_55 (* (/ 1194436035675977 1125899906842624) r1))) (let ((.def_56 (* (/ 5372398895734809 9007199254740992) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 4197928326647793 4503599627370496)))) (let ((.def_59 (or .def_15 .def_7 .def_58))) (let ((.def_60 (* (/ 3589421683158279 4503599627370496) r3))) (let ((.def_61 (* (- (/ 927834285482585 1125899906842624)) r2))) (let ((.def_62 (* (/ 1728232974696931 9007199254740992) r1))) (let ((.def_63 (* (/ 1140965045077081 4503599627370496) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 4389975584608359 9007199254740992)))) (let ((.def_66 (or .def_15 .def_7 .def_65))) (let ((.def_67 (* (/ 2655309897463473 4503599627370496) r3))) (let ((.def_68 (* (- (/ 8043713309583705 9007199254740992)) r2))) (let ((.def_69 (* (/ 3312672216543933 2251799813685248) r1))) (let ((.def_70 (* (- (/ 1646867223512007 2251799813685248)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 1866017145913529 2251799813685248)))) (let ((.def_73 (or .def_23 .def_7 .def_72))) (let ((.def_74 (* (/ 802479416322421 4503599627370496) r3))) (let ((.def_75 (* (- (/ 2033819617593925 2251799813685248)) r2))) (let ((.def_76 (* (- (/ 4278265936489085 4503599627370496)) r1))) (let ((.def_77 (* (/ 196052606830493 562949953421312) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 2703935798418241 9007199254740992))))) (let ((.def_80 (or b3 b1 .def_79))) (let ((.def_81 (* (- (/ 59945283890017 2251799813685248)) r3))) (let ((.def_82 (* (- (/ 2709292011515089 2251799813685248)) r2))) (let ((.def_83 (* (/ 4386783119317849 4503599627370496) r1))) (let ((.def_84 (* (/ 1190110692502507 2251799813685248) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 2398098001400443 4503599627370496)))) (let ((.def_87 (or .def_7 .def_6 .def_86))) (let ((.def_88 (* (- (/ 2502368830074461 9007199254740992)) r3))) (let ((.def_89 (* (/ 266850166093265 562949953421312) r2))) (let ((.def_90 (* (- (/ 511520850263305 562949953421312)) r1))) (let ((.def_91 (* (- (/ 190168806447061 4503599627370496)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 132991551925169 9007199254740992))))) (let ((.def_94 (or .def_6 .def_7 .def_93))) (let ((.def_95 (and .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_45 .def_38 .def_31 .def_24 .def_16 .def_8))) .def_95)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
