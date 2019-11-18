(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 617509156222491 1125899906842624) r3))) (let ((.def_1 (* (- (/ 1947565837982067 1125899906842624)) r2))) (let ((.def_2 (* (- (/ 6129418096621585 9007199254740992)) r1))) (let ((.def_3 (* (/ 3803936322008745 9007199254740992) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 716281941598171 2251799813685248))))) (let ((.def_6 (* (- (/ 5444359752955389 2251799813685248)) r3))) (let ((.def_7 (* (- (/ 1293122625162865 562949953421312)) r2))) (let ((.def_8 (* (- (/ 5191419529466077 2251799813685248)) r1))) (let ((.def_9 (* (/ 380941445937993 1125899906842624) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 8517920726120599 2251799813685248))))) (let ((.def_12 (or b0 .def_11 .def_5))) (let ((.def_13 (* (- (/ 2798149157356023 4503599627370496)) r3))) (let ((.def_14 (* (/ 70078111796813 140737488355328) r2))) (let ((.def_15 (* (- (/ 567068940906721 4503599627370496)) r1))) (let ((.def_16 (* (- (/ 1909239939323565 4503599627370496)) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (- (/ 2290519172584791 9007199254740992))))) (let ((.def_19 (* (- (/ 1256517944245047 562949953421312)) r3))) (let ((.def_20 (* (/ 2993693190449419 9007199254740992) r2))) (let ((.def_21 (* (/ 780108390531207 1125899906842624) r1))) (let ((.def_22 (* (/ 390629542599669 2251799813685248) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 3542403020845591 4503599627370496))))) (let ((.def_25 (not b0))) (let ((.def_26 (or .def_25 .def_24 .def_18))) (let ((.def_27 (* (/ 192088092483549 140737488355328) r3))) (let ((.def_28 (* (- (/ 1980266744264329 9007199254740992)) r2))) (let ((.def_29 (* (/ 5831641440532495 9007199254740992) r1))) (let ((.def_30 (* (- (/ 2176554016559997 2251799813685248)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 1403241367554119 4503599627370496)))) (let ((.def_33 (* (- (/ 1615716963062429 2251799813685248)) r3))) (let ((.def_34 (* (- (/ 3723661237460069 2251799813685248)) r2))) (let ((.def_35 (* (- (/ 502386507980123 281474976710656)) r1))) (let ((.def_36 (* (/ 4667189683260593 2251799813685248) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 2959695326721781 2251799813685248))))) (let ((.def_39 (not b2))) (let ((.def_40 (or .def_39 .def_38 .def_32))) (let ((.def_41 (* (- (/ 721966614469217 562949953421312)) r3))) (let ((.def_42 (* (/ 4516139541361579 2251799813685248) r2))) (let ((.def_43 (* (- (/ 6479324266824363 4503599627370496)) r1))) (let ((.def_44 (* (/ 245983847138027 1125899906842624) r0))) (let ((.def_45 (+ .def_44 .def_43 .def_42 .def_41))) (let ((.def_46 (<= .def_45 (/ 5630320566205675 9007199254740992)))) (let ((.def_47 (* (/ 8515826412899637 9007199254740992) r3))) (let ((.def_48 (* (/ 4304074980958205 2251799813685248) r2))) (let ((.def_49 (* (- (/ 5582631627225561 2251799813685248)) r1))) (let ((.def_50 (* (/ 3137005965425185 2251799813685248) r0))) (let ((.def_51 (+ .def_50 .def_49 .def_48 .def_47))) (let ((.def_52 (<= .def_51 (/ 7142208990928085 9007199254740992)))) (let ((.def_53 (or .def_25 .def_52 .def_46))) (let ((.def_54 (* (- (/ 99230540172469 70368744177664)) r3))) (let ((.def_55 (* (/ 226820293156887 281474976710656) r2))) (let ((.def_56 (* (/ 271387454858053 1125899906842624) r1))) (let ((.def_57 (* (- (/ 1579282014738389 4503599627370496)) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (- (/ 529605827898209 9007199254740992))))) (let ((.def_60 (* (/ 5793561430144413 9007199254740992) r3))) (let ((.def_61 (* (/ 219791122066937 281474976710656) r2))) (let ((.def_62 (* (/ 1690904018880833 9007199254740992) r1))) (let ((.def_63 (* (- (/ 8111610919133955 4503599627370496)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 2827213797000561 9007199254740992))))) (let ((.def_66 (or b1 .def_65 .def_59))) (let ((.def_67 (* (/ 2536920716522255 4503599627370496) r3))) (let ((.def_68 (* (/ 3875575502368595 9007199254740992) r2))) (let ((.def_69 (* (/ 474945330878223 1125899906842624) r1))) (let ((.def_70 (* (- (/ 8971066231363341 9007199254740992)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 407966444227075 2251799813685248)))) (let ((.def_73 (* (- (/ 1672547246290617 1125899906842624)) r3))) (let ((.def_74 (* (- (/ 2004514751480553 1125899906842624)) r2))) (let ((.def_75 (* (- (/ 8428580722107305 9007199254740992)) r1))) (let ((.def_76 (* (/ 3208681133352505 2251799813685248) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 3491664320242373 2251799813685248))))) (let ((.def_79 (not b3))) (let ((.def_80 (or .def_79 .def_78 .def_72))) (let ((.def_81 (* (/ 4458096244651211 4503599627370496) r3))) (let ((.def_82 (* (- (/ 4510119667488965 2251799813685248)) r2))) (let ((.def_83 (* (/ 1283865329367423 2251799813685248) r1))) (let ((.def_84 (* (/ 2807082531227807 9007199254740992) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 6095600159247061 9007199254740992)))) (let ((.def_87 (* (/ 950110207436391 562949953421312) r3))) (let ((.def_88 (* (- (/ 1612748472156591 2251799813685248)) r2))) (let ((.def_89 (* (/ 1353590523264475 4503599627370496) r1))) (let ((.def_90 (* (/ 748335858332011 9007199254740992) r0))) (let ((.def_91 (+ .def_90 .def_89 .def_88 .def_87))) (let ((.def_92 (<= .def_91 (/ 2595467832468991 4503599627370496)))) (let ((.def_93 (or .def_39 .def_92 .def_86))) (let ((.def_94 (* (- (/ 5587827737955239 9007199254740992)) r3))) (let ((.def_95 (* (- (/ 4767684108736077 9007199254740992)) r2))) (let ((.def_96 (* (/ 3238515288649463 4503599627370496) r1))) (let ((.def_97 (* (- (/ 3329593416632537 4503599627370496)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (- (/ 1072174925517297 9007199254740992))))) (let ((.def_100 (* (/ 6050708919449447 4503599627370496) r3))) (let ((.def_101 (* (- (/ 3641940107519497 2251799813685248)) r2))) (let ((.def_102 (* (/ 4828400978302041 9007199254740992) r1))) (let ((.def_103 (* (- (/ 4342464973748291 2251799813685248)) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (- (/ 128296587891521 140737488355328))))) (let ((.def_106 (or b3 .def_105 .def_99))) (let ((.def_107 (and .def_106 .def_93 .def_80 .def_66 .def_53 .def_40 .def_26 .def_12))) .def_107)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)