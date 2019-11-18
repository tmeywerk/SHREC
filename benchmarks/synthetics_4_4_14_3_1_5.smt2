(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (- (/ 1009973089739003 9007199254740992)) r3))) (let ((.def_1 (* (- (/ 759351094778675 562949953421312)) r2))) (let ((.def_2 (* (- (/ 8489625523149305 9007199254740992)) r1))) (let ((.def_3 (* (/ 74246092784573 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 2994713839622215 4503599627370496))))) (let ((.def_6 (not b2))) (let ((.def_7 (or .def_6 b3 .def_5))) (let ((.def_8 (* (/ 1465857591938567 1125899906842624) r3))) (let ((.def_9 (* (/ 2378789638965901 2251799813685248) r2))) (let ((.def_10 (* (- (/ 7086021686346645 9007199254740992)) r1))) (let ((.def_11 (* (/ 960191004642095 2251799813685248) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 706109946842385 562949953421312)))) (let ((.def_14 (not b1))) (let ((.def_15 (or b3 .def_14 .def_13))) (let ((.def_16 (* (/ 4276635215862567 9007199254740992) r3))) (let ((.def_17 (* (/ 4935189456689495 9007199254740992) r2))) (let ((.def_18 (* (- (/ 1004112865745407 562949953421312)) r1))) (let ((.def_19 (* (- (/ 3241613851883267 4503599627370496)) r0))) (let ((.def_20 (+ .def_19 .def_18 .def_17 .def_16))) (let ((.def_21 (<= .def_20 (- (/ 288509637547855 9007199254740992))))) (let ((.def_22 (not b0))) (let ((.def_23 (not b3))) (let ((.def_24 (or .def_23 .def_22 .def_21))) (let ((.def_25 (* (- (/ 3335185023857111 1125899906842624)) r3))) (let ((.def_26 (* (- (/ 548587660153619 562949953421312)) r2))) (let ((.def_27 (* (/ 7147259456931673 9007199254740992) r1))) (let ((.def_28 (* (/ 1951874967187397 2251799813685248) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (- (/ 3208112353747513 9007199254740992))))) (let ((.def_31 (or b3 .def_22 .def_30))) (let ((.def_32 (* (- (/ 1544295704626863 9007199254740992)) r3))) (let ((.def_33 (* (- (/ 4040543320752737 9007199254740992)) r2))) (let ((.def_34 (* (/ 3194080652441837 2251799813685248) r1))) (let ((.def_35 (* (/ 3693292329200599 2251799813685248) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (/ 4073988126288249 2251799813685248)))) (let ((.def_38 (or .def_6 b1 .def_37))) (let ((.def_39 (* (/ 26965763181359 281474976710656) r3))) (let ((.def_40 (* (- (/ 7524463661637 4503599627370496)) r2))) (let ((.def_41 (* (/ 3949792538224503 2251799813685248) r1))) (let ((.def_42 (* (- (/ 2335098740805705 2251799813685248)) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (/ 1043386414211239 1125899906842624)))) (let ((.def_45 (or .def_14 .def_6 .def_44))) (let ((.def_46 (* (/ 786943726662841 562949953421312) r3))) (let ((.def_47 (* (- (/ 338305952455927 9007199254740992)) r2))) (let ((.def_48 (* (/ 114508527223007 140737488355328) r1))) (let ((.def_49 (* (/ 3129711502851005 4503599627370496) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (/ 2163250792589803 1125899906842624)))) (let ((.def_52 (or .def_22 .def_14 .def_51))) (let ((.def_53 (* (/ 2525294003149763 2251799813685248) r3))) (let ((.def_54 (* (- (/ 5855367060022155 4503599627370496)) r2))) (let ((.def_55 (* (/ 1871169367380027 2251799813685248) r1))) (let ((.def_56 (* (- (/ 871094523388545 2251799813685248)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 3282182547908197 4503599627370496)))) (let ((.def_59 (or .def_14 b0 .def_58))) (let ((.def_60 (* (- (/ 1103398588781983 2251799813685248)) r3))) (let ((.def_61 (* (- (/ 1552654592723311 2251799813685248)) r2))) (let ((.def_62 (* (- (/ 424696891314495 562949953421312)) r1))) (let ((.def_63 (* (/ 1191444201249157 2251799813685248) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 786742141777249 2251799813685248))))) (let ((.def_66 (or b2 .def_22 .def_65))) (let ((.def_67 (* (/ 6989639052906515 9007199254740992) r3))) (let ((.def_68 (* (/ 666362230319491 562949953421312) r2))) (let ((.def_69 (* (/ 6857157699469827 9007199254740992) r1))) (let ((.def_70 (* (- (/ 3545007705115685 9007199254740992)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 7532414320739133 4503599627370496)))) (let ((.def_73 (or .def_14 b2 .def_72))) (let ((.def_74 (* (/ 277627247498219 4503599627370496) r3))) (let ((.def_75 (* (- (/ 488065185752863 562949953421312)) r2))) (let ((.def_76 (* (- (/ 2940252111060519 2251799813685248)) r1))) (let ((.def_77 (* (- (/ 2663117845776391 2251799813685248)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 4799096133721581 4503599627370496))))) (let ((.def_80 (or b2 b0 .def_79))) (let ((.def_81 (* (- (/ 3236367149117407 2251799813685248)) r3))) (let ((.def_82 (* (/ 1070299414747149 2251799813685248) r2))) (let ((.def_83 (* (/ 890489788614873 1125899906842624) r1))) (let ((.def_84 (* (/ 225290232518881 140737488355328) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 1543504580220805 1125899906842624)))) (let ((.def_87 (or .def_14 b3 .def_86))) (let ((.def_88 (* (- (/ 39898935531413 562949953421312)) r3))) (let ((.def_89 (* (- (/ 5916835327843345 9007199254740992)) r2))) (let ((.def_90 (* (- (/ 85291755292307 2251799813685248)) r1))) (let ((.def_91 (* (/ 2592546373056675 4503599627370496) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (/ 844686989744127 4503599627370496)))) (let ((.def_94 (or .def_23 b1 .def_93))) (let ((.def_95 (* (- (/ 676469630200891 562949953421312)) r3))) (let ((.def_96 (* (- (/ 1079766476667923 4503599627370496)) r2))) (let ((.def_97 (* (/ 1323209281774947 1125899906842624) r1))) (let ((.def_98 (* (/ 123425804715959 2251799813685248) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (/ 2035292657562377 4503599627370496)))) (let ((.def_101 (or .def_14 b2 .def_100))) (let ((.def_102 (and .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_45 .def_38 .def_31 .def_24 .def_15 .def_7))) .def_102))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)