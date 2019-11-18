(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun b3 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (/ 7670217808043445 9007199254740992) r3))) (let ((.def_1 (* (- (/ 4877512942888921 4503599627370496)) r2))) (let ((.def_2 (* (/ 55488074035661 70368744177664) r1))) (let ((.def_3 (* (/ 1597774627339641 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 5072331369552501 9007199254740992)))) (let ((.def_6 (or b2 b1 .def_5))) (let ((.def_7 (* (- (/ 2623444985556973 2251799813685248)) r3))) (let ((.def_8 (* (- (/ 1864025507455817 4503599627370496)) r2))) (let ((.def_9 (* (/ 6374568891228621 9007199254740992) r1))) (let ((.def_10 (* (/ 1490032359870093 4503599627370496) r0))) (let ((.def_11 (+ .def_10 .def_9 .def_8 .def_7))) (let ((.def_12 (<= .def_11 (- (/ 31836297387855 4503599627370496))))) (let ((.def_13 (not b0))) (let ((.def_14 (or b1 .def_13 .def_12))) (let ((.def_15 (* (- (/ 2734721254577413 1125899906842624)) r3))) (let ((.def_16 (* (/ 470693098794479 4503599627370496) r2))) (let ((.def_17 (* (- (/ 749001982456815 4503599627370496)) r1))) (let ((.def_18 (* (- (/ 30872612296955 4503599627370496)) r0))) (let ((.def_19 (+ .def_18 .def_17 .def_16 .def_15))) (let ((.def_20 (<= .def_19 (- (/ 655944586212781 1125899906842624))))) (let ((.def_21 (or b2 b3 .def_20))) (let ((.def_22 (* (/ 6386521783689111 9007199254740992) r3))) (let ((.def_23 (* (/ 1101610812222815 562949953421312) r2))) (let ((.def_24 (* (/ 1269193810822617 4503599627370496) r1))) (let ((.def_25 (* (/ 7281530407780889 4503599627370496) r0))) (let ((.def_26 (+ .def_25 .def_24 .def_23 .def_22))) (let ((.def_27 (<= .def_26 (/ 6775576912768123 2251799813685248)))) (let ((.def_28 (not b3))) (let ((.def_29 (or .def_28 b2 .def_27))) (let ((.def_30 (* (- (/ 474879764512113 4503599627370496)) r3))) (let ((.def_31 (* (- (/ 2137381954964105 2251799813685248)) r2))) (let ((.def_32 (* (/ 4243058842487821 4503599627370496) r1))) (let ((.def_33 (* (- (/ 2416530402181561 4503599627370496)) r0))) (let ((.def_34 (+ .def_33 .def_32 .def_31 .def_30))) (let ((.def_35 (<= .def_34 (/ 257746471937185 4503599627370496)))) (let ((.def_36 (or b2 b3 .def_35))) (let ((.def_37 (* (- (/ 1145154092908721 562949953421312)) r3))) (let ((.def_38 (* (/ 3223003422765033 4503599627370496) r2))) (let ((.def_39 (* (/ 436037215613361 4503599627370496) r1))) (let ((.def_40 (* (/ 916559282082883 9007199254740992) r0))) (let ((.def_41 (+ .def_40 .def_39 .def_38 .def_37))) (let ((.def_42 (<= .def_41 (/ 87666764808753 562949953421312)))) (let ((.def_43 (not b2))) (let ((.def_44 (or b1 .def_43 .def_42))) (let ((.def_45 (* (/ 3381186180817523 4503599627370496) r3))) (let ((.def_46 (* (- (/ 844995658698781 4503599627370496)) r2))) (let ((.def_47 (* (- (/ 7999694944499445 9007199254740992)) r1))) (let ((.def_48 (* (/ 250328863636591 2251799813685248) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 1082181630377211 4503599627370496)))) (let ((.def_51 (or .def_43 b1 .def_50))) (let ((.def_52 (* (/ 4270553690740485 4503599627370496) r3))) (let ((.def_53 (* (- (/ 7274128833937137 9007199254740992)) r2))) (let ((.def_54 (* (- (/ 1337938701579103 2251799813685248)) r1))) (let ((.def_55 (* (/ 895391493115103 1125899906842624) r0))) (let ((.def_56 (+ .def_55 .def_54 .def_53 .def_52))) (let ((.def_57 (<= .def_56 (/ 3899051525360079 9007199254740992)))) (let ((.def_58 (or b0 .def_28 .def_57))) (let ((.def_59 (* (- (/ 2540323629718927 2251799813685248)) r3))) (let ((.def_60 (* (- (/ 5683971441812235 4503599627370496)) r2))) (let ((.def_61 (* (/ 1107324966260317 1125899906842624) r1))) (let ((.def_62 (* (/ 187238167162545 1125899906842624) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (- (/ 700620357282103 4503599627370496))))) (let ((.def_65 (or b0 .def_28 .def_64))) (let ((.def_66 (* (/ 1384461694089383 2251799813685248) r3))) (let ((.def_67 (* (- (/ 3516806879219437 4503599627370496)) r2))) (let ((.def_68 (* (/ 184868330436829 2251799813685248) r1))) (let ((.def_69 (* (- (/ 2951720989936739 4503599627370496)) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (- (/ 182231791439643 9007199254740992))))) (let ((.def_72 (not b1))) (let ((.def_73 (or .def_72 b3 .def_71))) (let ((.def_74 (* (/ 2530056081220423 4503599627370496) r3))) (let ((.def_75 (* (- (/ 269380769553411 281474976710656)) r2))) (let ((.def_76 (* (/ 2716492208680875 2251799813685248) r1))) (let ((.def_77 (* (/ 1648250392588715 2251799813685248) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 1427297987118183 1125899906842624)))) (let ((.def_80 (or b0 b1 .def_79))) (let ((.def_81 (* (- (/ 392251470262789 4503599627370496)) r3))) (let ((.def_82 (* (- (/ 2015942475089453 4503599627370496)) r2))) (let ((.def_83 (* (- (/ 6989543689952277 9007199254740992)) r1))) (let ((.def_84 (* (/ 2202221386688319 2251799813685248) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 1318707043369919 4503599627370496)))) (let ((.def_87 (or b0 b1 .def_86))) (let ((.def_88 (* (- (/ 437293519281987 562949953421312)) r3))) (let ((.def_89 (* (- (/ 166084593744895 4503599627370496)) r2))) (let ((.def_90 (* (- (/ 6811132617210101 9007199254740992)) r1))) (let ((.def_91 (* (- (/ 7673257912890511 4503599627370496)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 4321001857035657 4503599627370496))))) (let ((.def_94 (or b0 b1 .def_93))) (let ((.def_95 (* (/ 1582823139961137 4503599627370496) r3))) (let ((.def_96 (* (/ 1907022616785809 9007199254740992) r2))) (let ((.def_97 (* (- (/ 1564385685894733 2251799813685248)) r1))) (let ((.def_98 (* (- (/ 2542357394741223 2251799813685248)) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (- (/ 27928145757381 281474976710656))))) (let ((.def_101 (or .def_72 b2 .def_100))) (let ((.def_102 (* (- (/ 2278219074823845 2251799813685248)) r3))) (let ((.def_103 (* (- (/ 1160420953600187 2251799813685248)) r2))) (let ((.def_104 (* (- (/ 2238466881733697 4503599627370496)) r1))) (let ((.def_105 (* (/ 928923006575391 9007199254740992) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (- (/ 2534325401467585 4503599627370496))))) (let ((.def_108 (or .def_28 b1 .def_107))) (let ((.def_109 (and .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_65 .def_58 .def_51 .def_44 .def_36 .def_29 .def_21 .def_14 .def_6))) .def_109)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)