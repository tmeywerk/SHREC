(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b0 () Bool)
(declare-fun r2 () Real)
(declare-fun b1 () Bool)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (- (/ 182644934447847 1125899906842624)) r3))) (let ((.def_1 (* (- (/ 1185005655241577 4503599627370496)) r2))) (let ((.def_2 (* (- (/ 419376092547937 562949953421312)) r1))) (let ((.def_3 (* (- (/ 535761815542895 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 336720264270549 562949953421312))))) (let ((.def_6 (* (- (/ 3968792528275567 4503599627370496)) r3))) (let ((.def_7 (* (/ 550647219205507 140737488355328) r2))) (let ((.def_8 (* (- (/ 2335153487666841 4503599627370496)) r1))) (let ((.def_9 (* (- (/ 87877627522007 140737488355328)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 6254108079906595 9007199254740992)))) (let ((.def_12 (not b1))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 998095930372789 9007199254740992)) r3))) (let ((.def_15 (* (/ 5720686151944591 4503599627370496) r2))) (let ((.def_16 (* (- (/ 1006724296126651 562949953421312)) r1))) (let ((.def_17 (* (- (/ 4281268867421981 9007199254740992)) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 1835769146363069 9007199254740992))))) (let ((.def_20 (* (- (/ 2696488265629305 9007199254740992)) r3))) (let ((.def_21 (* (/ 2714049101226441 2251799813685248) r2))) (let ((.def_22 (* (/ 4244376013269889 2251799813685248) r1))) (let ((.def_23 (* (/ 8557358842280999 2251799813685248) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 1743506042909093 562949953421312)))) (let ((.def_26 (not b0))) (let ((.def_27 (or .def_26 .def_25 .def_19))) (let ((.def_28 (* (- (/ 1227335501168525 4503599627370496)) r3))) (let ((.def_29 (* (- (/ 4669847328606287 9007199254740992)) r2))) (let ((.def_30 (* (- (/ 8166369468761613 4503599627370496)) r1))) (let ((.def_31 (* (- (/ 1130662828628421 2251799813685248)) r0))) (let ((.def_32 (+ .def_31 .def_30 .def_29 .def_28))) (let ((.def_33 (<= .def_32 (- (/ 4260253512398445 4503599627370496))))) (let ((.def_34 (* (/ 7136205723792913 9007199254740992) r3))) (let ((.def_35 (* (- (/ 4529818837072377 2251799813685248)) r2))) (let ((.def_36 (* (- (/ 4083335340539317 4503599627370496)) r1))) (let ((.def_37 (* (/ 1998569568912001 1125899906842624) r0))) (let ((.def_38 (+ .def_37 .def_36 .def_35 .def_34))) (let ((.def_39 (<= .def_38 (- (/ 3621534859558459 9007199254740992))))) (let ((.def_40 (or b1 .def_39 .def_33))) (let ((.def_41 (* (- (/ 624755535729805 2251799813685248)) r3))) (let ((.def_42 (* (- (/ 2328548594326081 2251799813685248)) r2))) (let ((.def_43 (* (/ 1435152197344265 4503599627370496) r1))) (let ((.def_44 (* (/ 2915434604599319 2251799813685248) r0))) (let ((.def_45 (+ .def_44 .def_43 .def_42 .def_41))) (let ((.def_46 (<= .def_45 (/ 839229116651695 4503599627370496)))) (let ((.def_47 (* (/ 1628748635356963 2251799813685248) r3))) (let ((.def_48 (* (/ 4032804232658095 4503599627370496) r2))) (let ((.def_49 (* (- (/ 5008637798251001 4503599627370496)) r1))) (let ((.def_50 (* (- (/ 8408661416718725 9007199254740992)) r0))) (let ((.def_51 (+ .def_50 .def_49 .def_48 .def_47))) (let ((.def_52 (<= .def_51 (- (/ 1621891812713179 4503599627370496))))) (let ((.def_53 (not b2))) (let ((.def_54 (or .def_53 .def_52 .def_46))) (let ((.def_55 (* (/ 4503549640621359 4503599627370496) r3))) (let ((.def_56 (* (- (/ 1878162863474527 2251799813685248)) r2))) (let ((.def_57 (* (- (/ 904925305842861 1125899906842624)) r1))) (let ((.def_58 (* (/ 2148245127939551 2251799813685248) r0))) (let ((.def_59 (+ .def_58 .def_57 .def_56 .def_55))) (let ((.def_60 (<= .def_59 (/ 1480277975985821 2251799813685248)))) (let ((.def_61 (* (/ 1338346273447469 1125899906842624) r3))) (let ((.def_62 (* (- (/ 407620373385587 140737488355328)) r2))) (let ((.def_63 (* (/ 864345851935911 4503599627370496) r1))) (let ((.def_64 (* (/ 4114287438154771 4503599627370496) r0))) (let ((.def_65 (+ .def_64 .def_63 .def_62 .def_61))) (let ((.def_66 (<= .def_65 (- (/ 4055141645613373 9007199254740992))))) (let ((.def_67 (or .def_12 .def_66 .def_60))) (let ((.def_68 (* (/ 1024996381392165 9007199254740992) r3))) (let ((.def_69 (* (- (/ 132275758033205 4503599627370496)) r2))) (let ((.def_70 (* (- (/ 2478191755643631 2251799813685248)) r1))) (let ((.def_71 (* (/ 4170516090662683 4503599627370496) r0))) (let ((.def_72 (+ .def_71 .def_70 .def_69 .def_68))) (let ((.def_73 (<= .def_72 (/ 259568490195029 4503599627370496)))) (let ((.def_74 (* (- (/ 2136775762470215 4503599627370496)) r3))) (let ((.def_75 (* (- (/ 2348405300989741 4503599627370496)) r2))) (let ((.def_76 (* (/ 948236165590903 2251799813685248) r1))) (let ((.def_77 (* (- (/ 1377599539603181 4503599627370496)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 1946192380573809 4503599627370496))))) (let ((.def_80 (not b3))) (let ((.def_81 (or .def_80 .def_79 .def_73))) (let ((.def_82 (* (/ 534225010850683 4503599627370496) r3))) (let ((.def_83 (* (/ 1130140604520105 2251799813685248) r2))) (let ((.def_84 (* (- (/ 2171134635634201 1125899906842624)) r1))) (let ((.def_85 (* (- (/ 1899875679221 2251799813685248)) r0))) (let ((.def_86 (+ .def_85 .def_84 .def_83 .def_82))) (let ((.def_87 (<= .def_86 (- (/ 1927740013532321 9007199254740992))))) (let ((.def_88 (* (- (/ 3506636461826275 2251799813685248)) r3))) (let ((.def_89 (* (- (/ 1692543277302099 2251799813685248)) r2))) (let ((.def_90 (* (- (/ 1049186428077079 4503599627370496)) r1))) (let ((.def_91 (* (/ 125777812727631 281474976710656) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 4703084480327037 4503599627370496))))) (let ((.def_94 (or .def_12 .def_93 .def_87))) (let ((.def_95 (* (/ 3828513914019907 2251799813685248) r3))) (let ((.def_96 (* (- (/ 2262965134929297 2251799813685248)) r2))) (let ((.def_97 (* (- (/ 2405534802484529 2251799813685248)) r1))) (let ((.def_98 (* (/ 735261962728203 2251799813685248) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (/ 2316824917652675 4503599627370496)))) (let ((.def_101 (* (- (/ 61971635476339 35184372088832)) r3))) (let ((.def_102 (* (/ 4671493780462841 2251799813685248) r2))) (let ((.def_103 (* (- (/ 348458509262413 140737488355328)) r1))) (let ((.def_104 (* (/ 1033145148046169 562949953421312) r0))) (let ((.def_105 (+ .def_104 .def_103 .def_102 .def_101))) (let ((.def_106 (<= .def_105 (- (/ 1356985329221475 9007199254740992))))) (let ((.def_107 (or b2 .def_106 .def_100))) (let ((.def_108 (* (/ 163852342372161 1125899906842624) r3))) (let ((.def_109 (* (- (/ 525765212104289 1125899906842624)) r2))) (let ((.def_110 (* (/ 2052129332077683 2251799813685248) r1))) (let ((.def_111 (* (- (/ 2184738246465679 4503599627370496)) r0))) (let ((.def_112 (+ .def_111 .def_110 .def_109 .def_108))) (let ((.def_113 (<= .def_112 (/ 1142844222402695 2251799813685248)))) (let ((.def_114 (* (/ 115228843532963 562949953421312) r3))) (let ((.def_115 (* (- (/ 4191749370906915 9007199254740992)) r2))) (let ((.def_116 (* (/ 3059559695812311 2251799813685248) r1))) (let ((.def_117 (* (/ 6032263497979663 9007199254740992) r0))) (let ((.def_118 (+ .def_117 .def_116 .def_115 .def_114))) (let ((.def_119 (<= .def_118 (/ 7423855775015017 9007199254740992)))) (let ((.def_120 (or b1 .def_119 .def_113))) (let ((.def_121 (* (/ 9712485143265 35184372088832) r3))) (let ((.def_122 (* (/ 2890229948933199 2251799813685248) r2))) (let ((.def_123 (* (/ 2773722792405525 4503599627370496) r1))) (let ((.def_124 (* (- (/ 2396308506578293 4503599627370496)) r0))) (let ((.def_125 (+ .def_124 .def_123 .def_122 .def_121))) (let ((.def_126 (<= .def_125 (/ 6308295525562807 4503599627370496)))) (let ((.def_127 (* (- (/ 8398992496323937 9007199254740992)) r3))) (let ((.def_128 (* (/ 3837089626760429 4503599627370496) r2))) (let ((.def_129 (* (- (/ 1595055658100403 1125899906842624)) r1))) (let ((.def_130 (* (- (/ 7974191663577139 2251799813685248)) r0))) (let ((.def_131 (+ .def_130 .def_129 .def_128 .def_127))) (let ((.def_132 (<= .def_131 (- (/ 6167355538284229 2251799813685248))))) (let ((.def_133 (or b0 .def_132 .def_126))) (let ((.def_134 (* (/ 3356783891391731 4503599627370496) r3))) (let ((.def_135 (* (- (/ 442789825436481 562949953421312)) r2))) (let ((.def_136 (* (- (/ 3436977340166227 4503599627370496)) r1))) (let ((.def_137 (* (- (/ 950701810752917 562949953421312)) r0))) (let ((.def_138 (+ .def_137 .def_136 .def_135 .def_134))) (let ((.def_139 (<= .def_138 (- (/ 7455558188167427 9007199254740992))))) (let ((.def_140 (* (/ 2356751931142257 9007199254740992) r3))) (let ((.def_141 (* (/ 766302634342771 562949953421312) r2))) (let ((.def_142 (* (/ 6646125652151585 9007199254740992) r1))) (let ((.def_143 (* (/ 1325322327032635 9007199254740992) r0))) (let ((.def_144 (+ .def_143 .def_142 .def_141 .def_140))) (let ((.def_145 (<= .def_144 (/ 2708970754344225 2251799813685248)))) (let ((.def_146 (or .def_53 .def_145 .def_139))) (let ((.def_147 (* (/ 2736362527001099 4503599627370496) r3))) (let ((.def_148 (* (- (/ 473769204829207 4503599627370496)) r2))) (let ((.def_149 (* (- (/ 1669682968753893 2251799813685248)) r1))) (let ((.def_150 (* (- (/ 2325403999448007 9007199254740992)) r0))) (let ((.def_151 (+ .def_150 .def_149 .def_148 .def_147))) (let ((.def_152 (<= .def_151 (/ 569148521077855 9007199254740992)))) (let ((.def_153 (* (/ 1145965457109417 1125899906842624) r3))) (let ((.def_154 (* (- (/ 2514696928087733 2251799813685248)) r2))) (let ((.def_155 (* (/ 5300273754793229 9007199254740992) r1))) (let ((.def_156 (* (/ 477964534956283 281474976710656) r0))) (let ((.def_157 (+ .def_156 .def_155 .def_154 .def_153))) (let ((.def_158 (<= .def_157 (/ 609998079027463 562949953421312)))) (let ((.def_159 (or .def_12 .def_158 .def_152))) (let ((.def_160 (and .def_159 .def_146 .def_133 .def_120 .def_107 .def_94 .def_81 .def_67 .def_54 .def_40 .def_27 .def_13))) .def_160))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
