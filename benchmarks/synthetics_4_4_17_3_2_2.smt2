(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun b2 () Bool)
(declare-fun r1 () Real)
(declare-fun b3 () Bool)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 54280958542631 281474976710656) r3))) (let ((.def_1 (* (/ 1242243894289299 2251799813685248) r2))) (let ((.def_2 (* (- (/ 380747084821607 140737488355328)) r1))) (let ((.def_3 (* (- (/ 1437086042970045 2251799813685248)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1447192770395035 2251799813685248))))) (let ((.def_6 (* (/ 7423549231720821 9007199254740992) r3))) (let ((.def_7 (* (- (/ 7231331985441315 9007199254740992)) r2))) (let ((.def_8 (* (/ 4100709837570295 4503599627370496) r1))) (let ((.def_9 (* (- (/ 6382660130723643 9007199254740992)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 22681150822943 2251799813685248))))) (let ((.def_12 (or b3 .def_11 .def_5))) (let ((.def_13 (* (- (/ 3910113124847443 9007199254740992)) r3))) (let ((.def_14 (* (- (/ 4174298506421397 2251799813685248)) r2))) (let ((.def_15 (* (- (/ 694244474014275 1125899906842624)) r1))) (let ((.def_16 (* (/ 4025162725528085 2251799813685248) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (/ 2310649674009357 9007199254740992)))) (let ((.def_19 (* (/ 6714234022533921 9007199254740992) r3))) (let ((.def_20 (* (/ 6499307534985777 9007199254740992) r2))) (let ((.def_21 (* (- (/ 2882966728757633 1125899906842624)) r1))) (let ((.def_22 (* (/ 2669005487516743 4503599627370496) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 4108143673009523 9007199254740992))))) (let ((.def_25 (or b2 .def_24 .def_18))) (let ((.def_26 (* (- (/ 5606897143952045 9007199254740992)) r3))) (let ((.def_27 (* (- (/ 5369933446656111 9007199254740992)) r2))) (let ((.def_28 (* (/ 3178214224693197 9007199254740992) r1))) (let ((.def_29 (* (- (/ 3645729071841881 4503599627370496)) r0))) (let ((.def_30 (+ .def_29 .def_28 .def_27 .def_26))) (let ((.def_31 (<= .def_30 (- (/ 3271852350587575 4503599627370496))))) (let ((.def_32 (* (/ 2519353441610213 1125899906842624) r3))) (let ((.def_33 (* (/ 2464598737238169 2251799813685248) r2))) (let ((.def_34 (* (/ 2297249036106981 4503599627370496) r1))) (let ((.def_35 (* (/ 1018768777575155 2251799813685248) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (/ 4749181042714593 2251799813685248)))) (let ((.def_38 (or b2 .def_37 .def_31))) (let ((.def_39 (* (- (/ 3076977937904173 4503599627370496)) r3))) (let ((.def_40 (* (- (/ 2182531939084635 9007199254740992)) r2))) (let ((.def_41 (* (- (/ 3467052396631289 9007199254740992)) r1))) (let ((.def_42 (* (/ 4408828441664473 4503599627370496) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (/ 355231065721421 2251799813685248)))) (let ((.def_45 (* (/ 2956767920826451 2251799813685248) r3))) (let ((.def_46 (* (/ 758072712209701 9007199254740992) r2))) (let ((.def_47 (* (- (/ 906678848400191 4503599627370496)) r1))) (let ((.def_48 (* (/ 220274375727193 562949953421312) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 3356625911805807 4503599627370496)))) (let ((.def_51 (not b3))) (let ((.def_52 (or .def_51 .def_50 .def_44))) (let ((.def_53 (* (/ 4955211014053183 9007199254740992) r3))) (let ((.def_54 (* (/ 4081087252348337 2251799813685248) r2))) (let ((.def_55 (* (/ 345638366533193 4503599627370496) r1))) (let ((.def_56 (* (- (/ 339205459392021 1125899906842624)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 3813912395765541 2251799813685248)))) (let ((.def_59 (* (/ 2747630322357541 2251799813685248) r3))) (let ((.def_60 (* (/ 3826793300462999 4503599627370496) r2))) (let ((.def_61 (* (- (/ 2449092452898381 1125899906842624)) r1))) (let ((.def_62 (* (- (/ 171798687070619 281474976710656)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (- (/ 446937979138699 1125899906842624))))) (let ((.def_65 (or b3 .def_64 .def_58))) (let ((.def_66 (* (- (/ 723613944805975 4503599627370496)) r3))) (let ((.def_67 (* (/ 2468292273073133 4503599627370496) r2))) (let ((.def_68 (* (- (/ 4349913453110679 4503599627370496)) r1))) (let ((.def_69 (* (/ 60877863090899 2251799813685248) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (/ 17081746479839 562949953421312)))) (let ((.def_72 (* (- (/ 760374004540603 1125899906842624)) r3))) (let ((.def_73 (* (/ 745250262083357 562949953421312) r2))) (let ((.def_74 (* (/ 2816874706442481 4503599627370496) r1))) (let ((.def_75 (* (- (/ 1949592412810093 4503599627370496)) r0))) (let ((.def_76 (+ .def_75 .def_74 .def_73 .def_72))) (let ((.def_77 (<= .def_76 (/ 1081179290557759 2251799813685248)))) (let ((.def_78 (or .def_51 .def_77 .def_71))) (let ((.def_79 (* (/ 2146156837745911 2251799813685248) r3))) (let ((.def_80 (* (- (/ 687543492705867 2251799813685248)) r2))) (let ((.def_81 (* (/ 243668861360629 9007199254740992) r1))) (let ((.def_82 (* (- (/ 311212767604739 1125899906842624)) r0))) (let ((.def_83 (+ .def_82 .def_81 .def_80 .def_79))) (let ((.def_84 (<= .def_83 (/ 368483784588253 1125899906842624)))) (let ((.def_85 (* (- (/ 2796912874540631 2251799813685248)) r3))) (let ((.def_86 (* (- (/ 1194511973984911 1125899906842624)) r2))) (let ((.def_87 (* (/ 4447125521083053 4503599627370496) r1))) (let ((.def_88 (* (- (/ 239089493007991 281474976710656)) r0))) (let ((.def_89 (+ .def_88 .def_87 .def_86 .def_85))) (let ((.def_90 (<= .def_89 (- (/ 2688567411195641 2251799813685248))))) (let ((.def_91 (not b2))) (let ((.def_92 (or .def_91 .def_90 .def_84))) (let ((.def_93 (* (/ 4088751191900441 9007199254740992) r3))) (let ((.def_94 (* (- (/ 4386961505028513 2251799813685248)) r2))) (let ((.def_95 (* (/ 722526668999821 4503599627370496) r1))) (let ((.def_96 (* (- (/ 527353770971331 9007199254740992)) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (- (/ 1709113585880839 9007199254740992))))) (let ((.def_99 (* (/ 2179952768414283 1125899906842624) r3))) (let ((.def_100 (* (/ 1252508776701703 4503599627370496) r2))) (let ((.def_101 (* (- (/ 1162267042780237 1125899906842624)) r1))) (let ((.def_102 (* (- (/ 1153301560611009 1125899906842624)) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (- (/ 70740702135385 9007199254740992))))) (let ((.def_105 (not b1))) (let ((.def_106 (or .def_105 .def_104 .def_98))) (let ((.def_107 (* (- (/ 1912807354547885 562949953421312)) r3))) (let ((.def_108 (* (/ 118811802005867 4503599627370496) r2))) (let ((.def_109 (* (- (/ 104247757957933 4503599627370496)) r1))) (let ((.def_110 (* (- (/ 682849716985751 1125899906842624)) r0))) (let ((.def_111 (+ .def_110 .def_109 .def_108 .def_107))) (let ((.def_112 (<= .def_111 (- (/ 3585134742486001 4503599627370496))))) (let ((.def_113 (* (- (/ 8878159428243677 9007199254740992)) r3))) (let ((.def_114 (* (- (/ 3713958180558889 2251799813685248)) r2))) (let ((.def_115 (* (/ 1262642221625073 562949953421312) r1))) (let ((.def_116 (* (/ 5415259170806417 2251799813685248) r0))) (let ((.def_117 (+ .def_116 .def_115 .def_114 .def_113))) (let ((.def_118 (<= .def_117 (/ 2621960815269175 2251799813685248)))) (let ((.def_119 (or b2 .def_118 .def_112))) (let ((.def_120 (* (/ 598763334970991 2251799813685248) r3))) (let ((.def_121 (* (/ 6015396794464791 2251799813685248) r2))) (let ((.def_122 (* (- (/ 6094869135717833 2251799813685248)) r1))) (let ((.def_123 (* (- (/ 1086926040521461 1125899906842624)) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (/ 2837120915377891 2251799813685248)))) (let ((.def_126 (* (/ 4895028982546109 9007199254740992) r3))) (let ((.def_127 (* (- (/ 1050652805272017 1125899906842624)) r2))) (let ((.def_128 (* (- (/ 5952879249527003 4503599627370496)) r1))) (let ((.def_129 (* (- (/ 1175450891501633 9007199254740992)) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (- (/ 2261293665266681 2251799813685248))))) (let ((.def_132 (or b2 .def_131 .def_125))) (let ((.def_133 (* (- (/ 3465342262255823 4503599627370496)) r3))) (let ((.def_134 (* (- (/ 3770232581746409 2251799813685248)) r2))) (let ((.def_135 (* (- (/ 2310415185808331 9007199254740992)) r1))) (let ((.def_136 (* (- (/ 2488474828010961 2251799813685248)) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 684027485185379 562949953421312))))) (let ((.def_139 (* (/ 3789785906516707 2251799813685248) r3))) (let ((.def_140 (* (- (/ 3414183598648781 1125899906842624)) r2))) (let ((.def_141 (* (/ 94180390181437 35184372088832) r1))) (let ((.def_142 (* (/ 376678477860629 562949953421312) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (/ 8057051995466561 9007199254740992)))) (let ((.def_145 (or b0 .def_144 .def_138))) (let ((.def_146 (* (/ 3037673484294285 4503599627370496) r3))) (let ((.def_147 (* (- (/ 3432788193555681 4503599627370496)) r2))) (let ((.def_148 (* (- (/ 1726750632901889 9007199254740992)) r1))) (let ((.def_149 (* (- (/ 2071748654414709 9007199254740992)) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 13010150506517 4503599627370496)))) (let ((.def_152 (* (/ 2458964790946315 4503599627370496) r3))) (let ((.def_153 (* (/ 161717021104967 4503599627370496) r2))) (let ((.def_154 (* (- (/ 2088330674712613 4503599627370496)) r1))) (let ((.def_155 (* (/ 2399766491086339 1125899906842624) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (/ 1451481631027329 1125899906842624)))) (let ((.def_158 (or .def_51 .def_157 .def_151))) (let ((.def_159 (* (- (/ 4493972671451565 9007199254740992)) r3))) (let ((.def_160 (* (/ 2473061641511651 9007199254740992) r2))) (let ((.def_161 (* (/ 779972948087167 1125899906842624) r1))) (let ((.def_162 (* (/ 298218294878761 2251799813685248) r0))) (let ((.def_163 (+ .def_162 .def_161 .def_160 .def_159))) (let ((.def_164 (<= .def_163 (/ 1577229036243329 4503599627370496)))) (let ((.def_165 (* (/ 1008706703886217 562949953421312) r3))) (let ((.def_166 (* (- (/ 722266666625703 4503599627370496)) r2))) (let ((.def_167 (* (- (/ 5299383244688365 4503599627370496)) r1))) (let ((.def_168 (* (- (/ 324016884035333 562949953421312)) r0))) (let ((.def_169 (+ .def_168 .def_167 .def_166 .def_165))) (let ((.def_170 (<= .def_169 (- (/ 522527428512487 4503599627370496))))) (let ((.def_171 (not b0))) (let ((.def_172 (or .def_171 .def_170 .def_164))) (let ((.def_173 (* (/ 3420179853408775 4503599627370496) r3))) (let ((.def_174 (* (- (/ 3314783834470699 4503599627370496)) r2))) (let ((.def_175 (* (- (/ 2565754049369045 4503599627370496)) r1))) (let ((.def_176 (* (- (/ 2206611278317559 9007199254740992)) r0))) (let ((.def_177 (+ .def_176 .def_175 .def_174 .def_173))) (let ((.def_178 (<= .def_177 (/ 177124673997599 2251799813685248)))) (let ((.def_179 (* (- (/ 5265653928945363 4503599627370496)) r3))) (let ((.def_180 (* (- (/ 1121715935128603 562949953421312)) r2))) (let ((.def_181 (* (/ 820189450264973 2251799813685248) r1))) (let ((.def_182 (* (- (/ 2069261076765507 2251799813685248)) r0))) (let ((.def_183 (+ .def_182 .def_181 .def_180 .def_179))) (let ((.def_184 (<= .def_183 (- (/ 1163337411000309 562949953421312))))) (let ((.def_185 (or .def_51 .def_184 .def_178))) (let ((.def_186 (* (- (/ 4221240792358539 2251799813685248)) r3))) (let ((.def_187 (* (- (/ 4456394272944229 9007199254740992)) r2))) (let ((.def_188 (* (- (/ 2792785246613687 2251799813685248)) r1))) (let ((.def_189 (* (/ 156251844068453 562949953421312) r0))) (let ((.def_190 (+ .def_189 .def_188 .def_187 .def_186))) (let ((.def_191 (<= .def_190 (- (/ 4084440301197823 4503599627370496))))) (let ((.def_192 (* (- (/ 1213536396972071 4503599627370496)) r3))) (let ((.def_193 (* (- (/ 1893058543623 562949953421312)) r2))) (let ((.def_194 (* (- (/ 27353519432793 2251799813685248)) r1))) (let ((.def_195 (* (- (/ 6021371741454625 4503599627370496)) r0))) (let ((.def_196 (+ .def_195 .def_194 .def_193 .def_192))) (let ((.def_197 (<= .def_196 (- (/ 266705904198733 281474976710656))))) (let ((.def_198 (or .def_51 .def_197 .def_191))) (let ((.def_199 (* (- (/ 735805370882187 9007199254740992)) r3))) (let ((.def_200 (* (- (/ 6522799156986897 2251799813685248)) r2))) (let ((.def_201 (* (- (/ 5539385610972387 9007199254740992)) r1))) (let ((.def_202 (* (/ 2661005028702681 2251799813685248) r0))) (let ((.def_203 (+ .def_202 .def_201 .def_200 .def_199))) (let ((.def_204 (<= .def_203 (/ 1105422805784021 9007199254740992)))) (let ((.def_205 (* (/ 3725172505804611 2251799813685248) r3))) (let ((.def_206 (* (- (/ 123526959464171 562949953421312)) r2))) (let ((.def_207 (* (- (/ 2019093058099347 9007199254740992)) r1))) (let ((.def_208 (* (/ 1772575749636013 9007199254740992) r0))) (let ((.def_209 (+ .def_208 .def_207 .def_206 .def_205))) (let ((.def_210 (<= .def_209 (/ 2882508366492863 4503599627370496)))) (let ((.def_211 (or .def_91 .def_210 .def_204))) (let ((.def_212 (* (/ 557792886717607 2251799813685248) r3))) (let ((.def_213 (* (- (/ 1256177217810271 2251799813685248)) r2))) (let ((.def_214 (* (/ 138749016869333 1125899906842624) r1))) (let ((.def_215 (* (- (/ 3361020010012499 2251799813685248)) r0))) (let ((.def_216 (+ .def_215 .def_214 .def_213 .def_212))) (let ((.def_217 (<= .def_216 (- (/ 447555285754783 4503599627370496))))) (let ((.def_218 (* (/ 177891471843391 281474976710656) r3))) (let ((.def_219 (* (- (/ 4860682287315743 2251799813685248)) r2))) (let ((.def_220 (* (/ 1487773723584387 1125899906842624) r1))) (let ((.def_221 (* (/ 339590603795299 1125899906842624) r0))) (let ((.def_222 (+ .def_221 .def_220 .def_219 .def_218))) (let ((.def_223 (<= .def_222 (/ 116033978117531 9007199254740992)))) (let ((.def_224 (or .def_91 .def_223 .def_217))) (let ((.def_225 (and .def_224 .def_211 .def_198 .def_185 .def_172 .def_158 .def_145 .def_132 .def_119 .def_106 .def_92 .def_78 .def_65 .def_52 .def_38 .def_25 .def_12))) .def_225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)