(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b2 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (/ 2736707470642167 2251799813685248) r3))) (let ((.def_1 (* (- (/ 173806051582929 281474976710656)) r2))) (let ((.def_2 (* (/ 7958571551604441 9007199254740992) r1))) (let ((.def_3 (* (- (/ 7642268662069461 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 1165219869116801 1125899906842624)))) (let ((.def_6 (* (- (/ 569382647869921 562949953421312)) r3))) (let ((.def_7 (* (- (/ 2420285360730863 4503599627370496)) r2))) (let ((.def_8 (* (/ 886844719186871 562949953421312) r1))) (let ((.def_9 (* (- (/ 1364091787424507 1125899906842624)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 1189870870518075 2251799813685248))))) (let ((.def_12 (not b1))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (/ 379596548183633 562949953421312) r3))) (let ((.def_15 (* (/ 519497099117879 562949953421312) r2))) (let ((.def_16 (* (- (/ 3386970193852927 2251799813685248)) r1))) (let ((.def_17 (* (/ 4708981207458183 9007199254740992) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (/ 1156092168049881 2251799813685248)))) (let ((.def_20 (* (/ 1510404497979407 1125899906842624) r3))) (let ((.def_21 (* (- (/ 1607634807668373 2251799813685248)) r2))) (let ((.def_22 (* (/ 1995492457583927 4503599627370496) r1))) (let ((.def_23 (* (- (/ 185165435339945 1125899906842624)) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 1365219984378593 4503599627370496)))) (let ((.def_26 (not b2))) (let ((.def_27 (or .def_26 .def_25 .def_19))) (let ((.def_28 (* (- (/ 2427348459845933 9007199254740992)) r3))) (let ((.def_29 (* (- (/ 6625199134659637 9007199254740992)) r2))) (let ((.def_30 (* (- (/ 7027159462395817 9007199254740992)) r1))) (let ((.def_31 (* (/ 1091653643853441 9007199254740992) r0))) (let ((.def_32 (+ .def_31 .def_30 .def_29 .def_28))) (let ((.def_33 (<= .def_32 (- (/ 5550928727190299 9007199254740992))))) (let ((.def_34 (* (/ 4637664031434561 2251799813685248) r3))) (let ((.def_35 (* (/ 1240829503202085 2251799813685248) r2))) (let ((.def_36 (* (- (/ 2313986117082855 4503599627370496)) r1))) (let ((.def_37 (* (- (/ 1143513927705543 2251799813685248)) r0))) (let ((.def_38 (+ .def_37 .def_36 .def_35 .def_34))) (let ((.def_39 (<= .def_38 (/ 5318935485047845 9007199254740992)))) (let ((.def_40 (or b3 .def_39 .def_33))) (let ((.def_41 (* (/ 2653899792582603 2251799813685248) r3))) (let ((.def_42 (* (- (/ 774311148267279 4503599627370496)) r2))) (let ((.def_43 (* (/ 2642535845384665 9007199254740992) r1))) (let ((.def_44 (* (/ 652315596105585 562949953421312) r0))) (let ((.def_45 (+ .def_44 .def_43 .def_42 .def_41))) (let ((.def_46 (<= .def_45 (/ 1390366782909081 1125899906842624)))) (let ((.def_47 (* (- (/ 778140703555709 4503599627370496)) r3))) (let ((.def_48 (* (/ 1073021117023207 9007199254740992) r2))) (let ((.def_49 (* (/ 1046905875975969 9007199254740992) r1))) (let ((.def_50 (* (- (/ 2698599993793523 2251799813685248)) r0))) (let ((.def_51 (+ .def_50 .def_49 .def_48 .def_47))) (let ((.def_52 (<= .def_51 (- (/ 682306572455481 1125899906842624))))) (let ((.def_53 (or b1 .def_52 .def_46))) (let ((.def_54 (* (/ 2690500057128555 2251799813685248) r3))) (let ((.def_55 (* (- (/ 197749724274241 562949953421312)) r2))) (let ((.def_56 (* (- (/ 2382351874360887 2251799813685248)) r1))) (let ((.def_57 (* (/ 2141330072807529 2251799813685248) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (/ 2514852932680355 2251799813685248)))) (let ((.def_60 (* (- (/ 1532808502239511 2251799813685248)) r3))) (let ((.def_61 (* (- (/ 198677341047901 140737488355328)) r2))) (let ((.def_62 (* (- (/ 2672908187257091 9007199254740992)) r1))) (let ((.def_63 (* (/ 5446217465733999 2251799813685248) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 304657447297671 9007199254740992)))) (let ((.def_66 (or b1 .def_65 .def_59))) (let ((.def_67 (* (- (/ 945473867645781 562949953421312)) r3))) (let ((.def_68 (* (/ 6235487651588617 4503599627370496) r2))) (let ((.def_69 (* (- (/ 1071071531752537 4503599627370496)) r1))) (let ((.def_70 (* (- (/ 1650189925188187 2251799813685248)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 257583547180063 1125899906842624))))) (let ((.def_73 (* (/ 2207808075214295 4503599627370496) r3))) (let ((.def_74 (* (- (/ 8128613101880195 9007199254740992)) r2))) (let ((.def_75 (* (/ 562631159441233 562949953421312) r1))) (let ((.def_76 (* (- (/ 8047082156757087 9007199254740992)) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 1113841597279981 9007199254740992))))) (let ((.def_79 (or b2 .def_78 .def_72))) (let ((.def_80 (* (- (/ 1792943772741923 2251799813685248)) r3))) (let ((.def_81 (* (/ 524688855720117 1125899906842624) r2))) (let ((.def_82 (* (/ 3483900935594749 4503599627370496) r1))) (let ((.def_83 (* (/ 439052376447729 1125899906842624) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 1224748348094539 2251799813685248)))) (let ((.def_86 (* (/ 5350761779611319 4503599627370496) r3))) (let ((.def_87 (* (/ 176738458813047 2251799813685248) r2))) (let ((.def_88 (* (- (/ 2477221876088561 9007199254740992)) r1))) (let ((.def_89 (* (/ 889100096750921 2251799813685248) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (/ 2787871001786581 4503599627370496)))) (let ((.def_92 (or b3 .def_91 .def_85))) (let ((.def_93 (* (- (/ 5750689188165399 9007199254740992)) r3))) (let ((.def_94 (* (- (/ 278922245619069 9007199254740992)) r2))) (let ((.def_95 (* (- (/ 2414943154312955 2251799813685248)) r1))) (let ((.def_96 (* (/ 5688425419146243 9007199254740992) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (- (/ 1268528138050809 9007199254740992))))) (let ((.def_99 (* (/ 3049536446086217 2251799813685248) r3))) (let ((.def_100 (* (- (/ 279213255983351 140737488355328)) r2))) (let ((.def_101 (* (- (/ 2306293374648105 9007199254740992)) r1))) (let ((.def_102 (* (/ 1185074342323135 562949953421312) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (/ 2630681591650281 4503599627370496)))) (let ((.def_105 (or b3 .def_104 .def_98))) (let ((.def_106 (* (/ 626070954250837 4503599627370496) r3))) (let ((.def_107 (* (/ 1997571319562523 4503599627370496) r2))) (let ((.def_108 (* (/ 3162609716684727 2251799813685248) r1))) (let ((.def_109 (* (- (/ 26963263666725 562949953421312)) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (/ 6890946483565409 4503599627370496)))) (let ((.def_112 (* (/ 780641600471625 4503599627370496) r3))) (let ((.def_113 (* (/ 4260503361300843 2251799813685248) r2))) (let ((.def_114 (* (/ 3036294276976797 2251799813685248) r1))) (let ((.def_115 (* (/ 4262195844712029 4503599627370496) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (/ 4791470057087463 2251799813685248)))) (let ((.def_118 (or .def_26 .def_117 .def_111))) (let ((.def_119 (* (- (/ 4422246282216951 9007199254740992)) r3))) (let ((.def_120 (* (/ 692260827459097 562949953421312) r2))) (let ((.def_121 (* (- (/ 4488252713768753 2251799813685248)) r1))) (let ((.def_122 (* (- (/ 847620614650351 4503599627370496)) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (/ 374852461435693 1125899906842624)))) (let ((.def_125 (* (- (/ 2460950484163289 2251799813685248)) r3))) (let ((.def_126 (* (/ 1297428493634127 9007199254740992) r2))) (let ((.def_127 (* (- (/ 609918698388229 281474976710656)) r1))) (let ((.def_128 (* (- (/ 90076839359661 35184372088832)) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (- (/ 397844529946639 140737488355328))))) (let ((.def_131 (or b0 .def_130 .def_124))) (let ((.def_132 (* (/ 497798919741871 2251799813685248) r3))) (let ((.def_133 (* (/ 408601878619977 1125899906842624) r2))) (let ((.def_134 (* (- (/ 439743267163251 1125899906842624)) r1))) (let ((.def_135 (* (/ 5155551104599931 9007199254740992) r0))) (let ((.def_136 (+ .def_135 .def_134 .def_133 .def_132))) (let ((.def_137 (<= .def_136 (/ 2169412800252097 4503599627370496)))) (let ((.def_138 (* (- (/ 1053131419626795 9007199254740992)) r3))) (let ((.def_139 (* (/ 2445079736178873 9007199254740992) r2))) (let ((.def_140 (* (/ 4181238827806861 2251799813685248) r1))) (let ((.def_141 (* (/ 2417489770829065 9007199254740992) r0))) (let ((.def_142 (+ .def_141 .def_140 .def_139 .def_138))) (let ((.def_143 (<= .def_142 (/ 3029818947079877 2251799813685248)))) (let ((.def_144 (or .def_12 .def_143 .def_137))) (let ((.def_145 (* (/ 5652102821715055 4503599627370496) r3))) (let ((.def_146 (* (- (/ 5824386608730167 9007199254740992)) r2))) (let ((.def_147 (* (- (/ 1819964009670967 2251799813685248)) r1))) (let ((.def_148 (* (- (/ 467973528916255 562949953421312)) r0))) (let ((.def_149 (+ .def_148 .def_147 .def_146 .def_145))) (let ((.def_150 (<= .def_149 (/ 290004879812255 1125899906842624)))) (let ((.def_151 (* (/ 1077831756737855 1125899906842624) r3))) (let ((.def_152 (* (- (/ 3827866000900251 2251799813685248)) r2))) (let ((.def_153 (* (/ 173283174391001 4503599627370496) r1))) (let ((.def_154 (* (- (/ 1463771862674365 4503599627370496)) r0))) (let ((.def_155 (+ .def_154 .def_153 .def_152 .def_151))) (let ((.def_156 (<= .def_155 (- (/ 1273431182824465 2251799813685248))))) (let ((.def_157 (or .def_26 .def_156 .def_150))) (let ((.def_158 (* (- (/ 3269941393894085 4503599627370496)) r3))) (let ((.def_159 (* (/ 872501140877451 562949953421312) r2))) (let ((.def_160 (* (- (/ 7252440927041651 9007199254740992)) r1))) (let ((.def_161 (* (- (/ 3610632225595875 4503599627370496)) r0))) (let ((.def_162 (+ .def_161 .def_160 .def_159 .def_158))) (let ((.def_163 (<= .def_162 (/ 4415427490920531 9007199254740992)))) (let ((.def_164 (* (- (/ 1329150360812767 9007199254740992)) r3))) (let ((.def_165 (* (/ 3396646890200657 2251799813685248) r2))) (let ((.def_166 (* (/ 12150022436603 1125899906842624) r1))) (let ((.def_167 (* (- (/ 991472125603349 4503599627370496)) r0))) (let ((.def_168 (+ .def_167 .def_166 .def_165 .def_164))) (let ((.def_169 (<= .def_168 (/ 2397164989591881 4503599627370496)))) (let ((.def_170 (not b0))) (let ((.def_171 (or .def_170 .def_169 .def_163))) (let ((.def_172 (and .def_171 .def_157 .def_144 .def_131 .def_118 .def_105 .def_92 .def_79 .def_66 .def_53 .def_40 .def_27 .def_13))) .def_172))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
