(set-logic QF_LRA)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (- (/ 2033538309865025 1125899906842624)) r3))) (let ((.def_1 (* (- (/ 6116971092033085 9007199254740992)) r2))) (let ((.def_2 (* (/ 1254559949813655 4503599627370496) r1))) (let ((.def_3 (* (- (/ 4143242067995939 9007199254740992)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1438661048875355 2251799813685248))))) (let ((.def_6 (not b2))) (let ((.def_7 (or b1 .def_6 .def_5))) (let ((.def_8 (* (/ 433098810808743 2251799813685248) r3))) (let ((.def_9 (* (- (/ 7534512607321185 9007199254740992)) r2))) (let ((.def_10 (* (/ 643514069097703 1125899906842624) r1))) (let ((.def_11 (* (- (/ 3931312523856955 9007199254740992)) r0))) (let ((.def_12 (+ .def_11 .def_10 .def_9 .def_8))) (let ((.def_13 (<= .def_12 (/ 589305143787565 9007199254740992)))) (let ((.def_14 (not b3))) (let ((.def_15 (not b0))) (let ((.def_16 (or .def_15 .def_14 .def_13))) (let ((.def_17 (* (/ 288403302077947 1125899906842624) r3))) (let ((.def_18 (* (/ 5996778716244487 9007199254740992) r2))) (let ((.def_19 (* (- (/ 1080928835495425 9007199254740992)) r1))) (let ((.def_20 (* (- (/ 5141974464125881 9007199254740992)) r0))) (let ((.def_21 (+ .def_20 .def_19 .def_18 .def_17))) (let ((.def_22 (<= .def_21 (/ 1774932079349179 4503599627370496)))) (let ((.def_23 (not b1))) (let ((.def_24 (or .def_6 .def_23 .def_22))) (let ((.def_25 (* (/ 2317020198522189 2251799813685248) r3))) (let ((.def_26 (* (- (/ 872370904132793 9007199254740992)) r2))) (let ((.def_27 (* (- (/ 2076806154649895 2251799813685248)) r1))) (let ((.def_28 (* (/ 680472130229315 2251799813685248) r0))) (let ((.def_29 (+ .def_28 .def_27 .def_26 .def_25))) (let ((.def_30 (<= .def_29 (/ 7457016539630405 9007199254740992)))) (let ((.def_31 (or b0 b3 .def_30))) (let ((.def_32 (* (- (/ 117075831621419 1125899906842624)) r3))) (let ((.def_33 (* (/ 5543091692058539 4503599627370496) r2))) (let ((.def_34 (* (/ 1692697249411805 2251799813685248) r1))) (let ((.def_35 (* (- (/ 1469934868291931 1125899906842624)) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (/ 1568788065916269 2251799813685248)))) (let ((.def_38 (or b3 b1 .def_37))) (let ((.def_39 (* (- (/ 595996164274741 562949953421312)) r3))) (let ((.def_40 (* (/ 1165060168538017 4503599627370496) r2))) (let ((.def_41 (* (/ 63921076562953 2251799813685248) r1))) (let ((.def_42 (* (- (/ 1671267257327545 2251799813685248)) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (- (/ 1068814286252667 4503599627370496))))) (let ((.def_45 (or b3 b1 .def_44))) (let ((.def_46 (* (/ 652535051626049 1125899906842624) r3))) (let ((.def_47 (* (/ 334420015589317 9007199254740992) r2))) (let ((.def_48 (* (- (/ 1799993653041789 4503599627370496)) r1))) (let ((.def_49 (* (- (/ 2951801368872071 1125899906842624)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 1472756246185403 9007199254740992))))) (let ((.def_52 (or b1 b0 .def_51))) (let ((.def_53 (* (/ 766490636565453 9007199254740992) r3))) (let ((.def_54 (* (- (/ 955665293873235 562949953421312)) r2))) (let ((.def_55 (* (- (/ 452987447737363 2251799813685248)) r1))) (let ((.def_56 (* (- (/ 160573087007159 2251799813685248)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (- (/ 830881562904405 2251799813685248))))) (let ((.def_59 (or b3 .def_6 .def_58))) (let ((.def_60 (* (- (/ 1538018163527607 1125899906842624)) r3))) (let ((.def_61 (* (- (/ 539999376416629 562949953421312)) r2))) (let ((.def_62 (* (/ 399802745916609 2251799813685248) r1))) (let ((.def_63 (* (/ 4157150598047931 9007199254740992) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 240192213732459 562949953421312))))) (let ((.def_66 (or .def_6 .def_23 .def_65))) (let ((.def_67 (* (/ 260329823414939 4503599627370496) r3))) (let ((.def_68 (* (- (/ 3561735208660513 2251799813685248)) r2))) (let ((.def_69 (* (- (/ 97774239385675 281474976710656)) r1))) (let ((.def_70 (* (- (/ 2191690838913383 9007199254740992)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 3910847983646973 9007199254740992))))) (let ((.def_73 (or .def_23 .def_15 .def_72))) (let ((.def_74 (* (- (/ 5851318438275383 2251799813685248)) r3))) (let ((.def_75 (* (/ 1347635442726631 4503599627370496) r2))) (let ((.def_76 (* (/ 4324688704307445 4503599627370496) r1))) (let ((.def_77 (* (/ 4929947677803615 9007199254740992) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 2762101756933045 4503599627370496)))) (let ((.def_80 (or b2 .def_14 .def_79))) (let ((.def_81 (* (- (/ 4739467586202223 2251799813685248)) r3))) (let ((.def_82 (* (/ 548642112470483 1125899906842624) r2))) (let ((.def_83 (* (- (/ 4903563692038697 9007199254740992)) r1))) (let ((.def_84 (* (- (/ 4256740036441211 4503599627370496)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (- (/ 6513879374771007 9007199254740992))))) (let ((.def_87 (or b0 .def_23 .def_86))) (let ((.def_88 (* (/ 645133078469273 4503599627370496) r3))) (let ((.def_89 (* (/ 255160844936113 562949953421312) r2))) (let ((.def_90 (* (- (/ 4408320552479401 4503599627370496)) r1))) (let ((.def_91 (* (- (/ 3147734015072195 2251799813685248)) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (- (/ 2074514950798917 9007199254740992))))) (let ((.def_94 (or .def_15 .def_23 .def_93))) (let ((.def_95 (* (/ 179652683264933 4503599627370496) r3))) (let ((.def_96 (* (- (/ 2383623929081561 9007199254740992)) r2))) (let ((.def_97 (* (/ 344047961365323 4503599627370496) r1))) (let ((.def_98 (* (/ 1163085965770147 4503599627370496) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (/ 921265340355219 4503599627370496)))) (let ((.def_101 (or .def_23 b2 .def_100))) (let ((.def_102 (* (/ 1407937998923859 4503599627370496) r3))) (let ((.def_103 (* (/ 1716711658023805 2251799813685248) r2))) (let ((.def_104 (* (- (/ 1197117794498519 9007199254740992)) r1))) (let ((.def_105 (* (- (/ 614032232193577 2251799813685248)) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (/ 3128577461114005 4503599627370496)))) (let ((.def_108 (or b3 b1 .def_107))) (let ((.def_109 (* (/ 5196092654583449 9007199254740992) r3))) (let ((.def_110 (* (- (/ 4273655445501471 9007199254740992)) r2))) (let ((.def_111 (* (/ 2949190456223435 4503599627370496) r1))) (let ((.def_112 (* (/ 1694701558898007 9007199254740992) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (/ 1887854501441161 2251799813685248)))) (let ((.def_115 (or .def_15 .def_6 .def_114))) (let ((.def_116 (* (- (/ 4339468390010857 9007199254740992)) r3))) (let ((.def_117 (* (/ 3679802524751571 9007199254740992) r2))) (let ((.def_118 (* (/ 1869833232424453 4503599627370496) r1))) (let ((.def_119 (* (- (/ 2290090171960093 4503599627370496)) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (/ 712077768915541 2251799813685248)))) (let ((.def_122 (or b1 .def_15 .def_121))) (let ((.def_123 (* (- (/ 1456761019023513 9007199254740992)) r3))) (let ((.def_124 (* (- (/ 2475109645438535 2251799813685248)) r2))) (let ((.def_125 (* (- (/ 2509464643039381 2251799813685248)) r1))) (let ((.def_126 (* (/ 7332815797582119 9007199254740992) r0))) (let ((.def_127 (+ .def_126 .def_125 .def_124 .def_123))) (let ((.def_128 (<= .def_127 (- (/ 2360337862146527 9007199254740992))))) (let ((.def_129 (or .def_15 b1 .def_128))) (let ((.def_130 (* (- (/ 1758139556724311 2251799813685248)) r3))) (let ((.def_131 (* (/ 110576184446797 140737488355328) r2))) (let ((.def_132 (* (- (/ 717492886771369 1125899906842624)) r1))) (let ((.def_133 (* (/ 780938923653259 4503599627370496) r0))) (let ((.def_134 (+ .def_133 .def_132 .def_131 .def_130))) (let ((.def_135 (<= .def_134 (/ 165067846878557 562949953421312)))) (let ((.def_136 (or b3 .def_23 .def_135))) (let ((.def_137 (* (/ 8174593009811849 4503599627370496) r3))) (let ((.def_138 (* (- (/ 1201796215213473 562949953421312)) r2))) (let ((.def_139 (* (- (/ 7193108333623003 9007199254740992)) r1))) (let ((.def_140 (* (/ 1048799421569535 4503599627370496) r0))) (let ((.def_141 (+ .def_140 .def_139 .def_138 .def_137))) (let ((.def_142 (<= .def_141 (/ 3106057452035463 9007199254740992)))) (let ((.def_143 (or b1 .def_15 .def_142))) (let ((.def_144 (* (/ 489991186250741 9007199254740992) r3))) (let ((.def_145 (* (/ 308643902373793 2251799813685248) r2))) (let ((.def_146 (* (- (/ 2699429904439923 9007199254740992)) r1))) (let ((.def_147 (* (/ 7007498021420929 9007199254740992) r0))) (let ((.def_148 (+ .def_147 .def_146 .def_145 .def_144))) (let ((.def_149 (<= .def_148 (/ 376597715689557 562949953421312)))) (let ((.def_150 (or .def_14 .def_6 .def_149))) (let ((.def_151 (* (/ 5837205908246733 9007199254740992) r3))) (let ((.def_152 (* (- (/ 1232175211684007 562949953421312)) r2))) (let ((.def_153 (* (/ 2732140520081835 2251799813685248) r1))) (let ((.def_154 (* (/ 199007730889119 2251799813685248) r0))) (let ((.def_155 (+ .def_154 .def_153 .def_152 .def_151))) (let ((.def_156 (<= .def_155 (/ 998358760092131 1125899906842624)))) (let ((.def_157 (or .def_15 .def_14 .def_156))) (let ((.def_158 (* (/ 4100874227061545 4503599627370496) r3))) (let ((.def_159 (* (- (/ 3072077810388885 4503599627370496)) r2))) (let ((.def_160 (* (- (/ 2290188210033429 4503599627370496)) r1))) (let ((.def_161 (* (/ 1687469973748383 9007199254740992) r0))) (let ((.def_162 (+ .def_161 .def_160 .def_159 .def_158))) (let ((.def_163 (<= .def_162 (/ 1946751435957641 4503599627370496)))) (let ((.def_164 (or b1 .def_15 .def_163))) (let ((.def_165 (* (- (/ 1955150956170937 2251799813685248)) r3))) (let ((.def_166 (* (- (/ 2194134983319931 4503599627370496)) r2))) (let ((.def_167 (* (/ 3297321456736183 2251799813685248) r1))) (let ((.def_168 (* (/ 358783055105547 1125899906842624) r0))) (let ((.def_169 (+ .def_168 .def_167 .def_166 .def_165))) (let ((.def_170 (<= .def_169 (/ 126030343060527 140737488355328)))) (let ((.def_171 (or .def_14 .def_23 .def_170))) (let ((.def_172 (* (- (/ 730443511701539 1125899906842624)) r3))) (let ((.def_173 (* (- (/ 553783601752405 2251799813685248)) r2))) (let ((.def_174 (* (- (/ 3659209022665513 2251799813685248)) r1))) (let ((.def_175 (* (- (/ 899066513614005 2251799813685248)) r0))) (let ((.def_176 (+ .def_175 .def_174 .def_173 .def_172))) (let ((.def_177 (<= .def_176 (- (/ 6819946572126975 9007199254740992))))) (let ((.def_178 (or .def_23 b2 .def_177))) (let ((.def_179 (and .def_178 .def_171 .def_164 .def_157 .def_150 .def_143 .def_136 .def_129 .def_122 .def_115 .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_45 .def_38 .def_31 .def_24 .def_16 .def_7))) .def_179)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)