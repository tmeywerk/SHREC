(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b1 () Bool)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 504436554914213 9007199254740992) r3))) (let ((.def_1 (* (- (/ 4331476807586361 4503599627370496)) r2))) (let ((.def_2 (* (/ 3508885240282691 4503599627370496) r1))) (let ((.def_3 (* (- (/ 3225551746653391 2251799813685248)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 2652872804325373 9007199254740992))))) (let ((.def_6 (* (- (/ 3228962064929431 9007199254740992)) r3))) (let ((.def_7 (* (/ 402456925537911 2251799813685248) r2))) (let ((.def_8 (* (- (/ 1939446847230185 4503599627370496)) r1))) (let ((.def_9 (* (- (/ 1701903330141493 1125899906842624)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 2857706411575337 2251799813685248))))) (let ((.def_12 (or b2 .def_11 .def_5))) (let ((.def_13 (* (- (/ 591221077236611 2251799813685248)) r3))) (let ((.def_14 (* (- (/ 4408421423915965 4503599627370496)) r2))) (let ((.def_15 (* (/ 870660087737001 1125899906842624) r1))) (let ((.def_16 (* (/ 2699828538232465 4503599627370496) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (/ 3949552869477319 9007199254740992)))) (let ((.def_19 (* (/ 3328495816760503 2251799813685248) r3))) (let ((.def_20 (* (- (/ 915473687991741 2251799813685248)) r2))) (let ((.def_21 (* (- (/ 3326126970069611 2251799813685248)) r1))) (let ((.def_22 (* (/ 1359925697336959 9007199254740992) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 4850887774686263 9007199254740992))))) (let ((.def_25 (or b3 .def_24 .def_18))) (let ((.def_26 (* (- (/ 6400488947360907 9007199254740992)) r3))) (let ((.def_27 (* (/ 5050233430875353 4503599627370496) r2))) (let ((.def_28 (* (- (/ 4247491823475065 2251799813685248)) r1))) (let ((.def_29 (* (- (/ 3614013428801775 1125899906842624)) r0))) (let ((.def_30 (+ .def_29 .def_28 .def_27 .def_26))) (let ((.def_31 (<= .def_30 (- (/ 5133771878385221 4503599627370496))))) (let ((.def_32 (* (- (/ 1411672153532517 2251799813685248)) r3))) (let ((.def_33 (* (/ 4782790378634365 4503599627370496) r2))) (let ((.def_34 (* (- (/ 1997209073869949 9007199254740992)) r1))) (let ((.def_35 (* (- (/ 1389623241269497 9007199254740992)) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (/ 46607845397709 4503599627370496)))) (let ((.def_38 (or b3 .def_37 .def_31))) (let ((.def_39 (* (/ 91643796037077 562949953421312) r3))) (let ((.def_40 (* (/ 1652524906818865 4503599627370496) r2))) (let ((.def_41 (* (- (/ 3257366389988185 9007199254740992)) r1))) (let ((.def_42 (* (/ 8427366340103765 9007199254740992) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (/ 8249392763721709 9007199254740992)))) (let ((.def_45 (* (- (/ 7266930111068453 9007199254740992)) r3))) (let ((.def_46 (* (- (/ 4007586002915953 4503599627370496)) r2))) (let ((.def_47 (* (- (/ 3687791495282779 4503599627370496)) r1))) (let ((.def_48 (* (/ 468447776767645 562949953421312) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (- (/ 3782245608695 4398046511104))))) (let ((.def_51 (not b0))) (let ((.def_52 (or .def_51 .def_50 .def_44))) (let ((.def_53 (* (- (/ 96489261379085 562949953421312)) r3))) (let ((.def_54 (* (- (/ 229873286535371 562949953421312)) r2))) (let ((.def_55 (* (- (/ 463082341029055 2251799813685248)) r1))) (let ((.def_56 (* (/ 1556612519651261 1125899906842624) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 5621731392840285 9007199254740992)))) (let ((.def_59 (* (- (/ 2079819729764827 4503599627370496)) r3))) (let ((.def_60 (* (/ 2876190900427841 2251799813685248) r2))) (let ((.def_61 (* (/ 1158981368890655 1125899906842624) r1))) (let ((.def_62 (* (- (/ 1154840986505937 1125899906842624)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 2252907219557411 9007199254740992)))) (let ((.def_65 (or b2 .def_64 .def_58))) (let ((.def_66 (* (- (/ 5459468399028063 2251799813685248)) r3))) (let ((.def_67 (* (/ 198332451121063 4503599627370496) r2))) (let ((.def_68 (* (/ 494522118762769 2251799813685248) r1))) (let ((.def_69 (* (- (/ 76100232824893 70368744177664)) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (- (/ 2978374124865771 2251799813685248))))) (let ((.def_72 (* (/ 4430062034948375 2251799813685248) r3))) (let ((.def_73 (* (/ 2066958695331013 2251799813685248) r2))) (let ((.def_74 (* (- (/ 3097651083356127 9007199254740992)) r1))) (let ((.def_75 (* (- (/ 1538010206096783 1125899906842624)) r0))) (let ((.def_76 (+ .def_75 .def_74 .def_73 .def_72))) (let ((.def_77 (<= .def_76 (/ 854937351803629 2251799813685248)))) (let ((.def_78 (or b2 .def_77 .def_71))) (let ((.def_79 (* (/ 2802589162839829 4503599627370496) r3))) (let ((.def_80 (* (/ 5953346092310705 9007199254740992) r2))) (let ((.def_81 (* (- (/ 2991772312859009 2251799813685248)) r1))) (let ((.def_82 (* (/ 7036558455072607 9007199254740992) r0))) (let ((.def_83 (+ .def_82 .def_81 .def_80 .def_79))) (let ((.def_84 (<= .def_83 (/ 4230671964747975 4503599627370496)))) (let ((.def_85 (* (/ 7345191065561987 9007199254740992) r3))) (let ((.def_86 (* (- (/ 3363697883059317 4503599627370496)) r2))) (let ((.def_87 (* (/ 5752705510978191 9007199254740992) r1))) (let ((.def_88 (* (/ 265896245310435 2251799813685248) r0))) (let ((.def_89 (+ .def_88 .def_87 .def_86 .def_85))) (let ((.def_90 (<= .def_89 (/ 82679562994695 281474976710656)))) (let ((.def_91 (or .def_51 .def_90 .def_84))) (let ((.def_92 (* (/ 2484828875799315 4503599627370496) r3))) (let ((.def_93 (* (/ 448722798313015 4503599627370496) r2))) (let ((.def_94 (* (- (/ 8198353396738153 9007199254740992)) r1))) (let ((.def_95 (* (- (/ 4142447751801003 2251799813685248)) r0))) (let ((.def_96 (+ .def_95 .def_94 .def_93 .def_92))) (let ((.def_97 (<= .def_96 (- (/ 1311532115647597 4503599627370496))))) (let ((.def_98 (* (- (/ 156337438009599 9007199254740992)) r3))) (let ((.def_99 (* (- (/ 2095474835742309 1125899906842624)) r2))) (let ((.def_100 (* (/ 3838748237196979 9007199254740992) r1))) (let ((.def_101 (* (- (/ 1215318974476957 2251799813685248)) r0))) (let ((.def_102 (+ .def_101 .def_100 .def_99 .def_98))) (let ((.def_103 (<= .def_102 (- (/ 2562495583174901 2251799813685248))))) (let ((.def_104 (not b2))) (let ((.def_105 (or .def_104 .def_103 .def_97))) (let ((.def_106 (* (/ 887190772298301 1125899906842624) r3))) (let ((.def_107 (* (/ 2395842816423299 2251799813685248) r2))) (let ((.def_108 (* (/ 4948605924377667 4503599627370496) r1))) (let ((.def_109 (* (- (/ 531860408186817 562949953421312)) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (/ 695779548526139 562949953421312)))) (let ((.def_112 (* (- (/ 2819340176606323 9007199254740992)) r3))) (let ((.def_113 (* (- (/ 1117760921164193 9007199254740992)) r2))) (let ((.def_114 (* (- (/ 3779994184948927 1125899906842624)) r1))) (let ((.def_115 (* (/ 260665809700523 70368744177664) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (- (/ 583811548709493 9007199254740992))))) (let ((.def_118 (or b3 .def_117 .def_111))) (let ((.def_119 (* (/ 3132281582793967 4503599627370496) r3))) (let ((.def_120 (* (- (/ 546530072630971 4503599627370496)) r2))) (let ((.def_121 (* (- (/ 2550247185518319 4503599627370496)) r1))) (let ((.def_122 (* (- (/ 1411534968809837 2251799813685248)) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (- (/ 786892390053741 2251799813685248))))) (let ((.def_125 (* (- (/ 5981488056407219 9007199254740992)) r3))) (let ((.def_126 (* (/ 277340988847545 4503599627370496) r2))) (let ((.def_127 (* (/ 2970098081546381 2251799813685248) r1))) (let ((.def_128 (* (/ 8990817187459263 9007199254740992) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (/ 7778745917775941 9007199254740992)))) (let ((.def_131 (not b1))) (let ((.def_132 (or .def_131 .def_130 .def_124))) (let ((.def_133 (* (- (/ 68647088055835 2251799813685248)) r3))) (let ((.def_134 (* (- (/ 7601298132937769 9007199254740992)) r2))) (let ((.def_135 (* (- (/ 5099621184344551 9007199254740992)) r1))) (let ((.def_136 (* (- (/ 2467949217735671 4503599627370496)) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 587248086382749 1125899906842624))))) (let ((.def_139 (* (- (/ 2268636993454529 9007199254740992)) r3))) (let ((.def_140 (* (- (/ 1501590013501047 1125899906842624)) r2))) (let ((.def_141 (* (/ 2454747128880931 4503599627370496) r1))) (let ((.def_142 (* (/ 95921688771549 2251799813685248) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (- (/ 2348695925173895 4503599627370496))))) (let ((.def_145 (or b2 .def_144 .def_138))) (let ((.def_146 (* (/ 129827682383733 281474976710656) r3))) (let ((.def_147 (* (- (/ 3389491082478143 4503599627370496)) r2))) (let ((.def_148 (* (- (/ 2345999479496093 9007199254740992)) r1))) (let ((.def_149 (* (/ 3967518409807515 4503599627370496) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 2648210933599049 4503599627370496)))) (let ((.def_152 (* (- (/ 3171214004697653 4503599627370496)) r3))) (let ((.def_153 (* (- (/ 6642384755798615 9007199254740992)) r2))) (let ((.def_154 (* (/ 1494933141233641 1125899906842624) r1))) (let ((.def_155 (* (/ 5485381864782651 9007199254740992) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (/ 51872844275019 281474976710656)))) (let ((.def_158 (or .def_104 .def_157 .def_151))) (let ((.def_159 (* (/ 1813638444927123 4503599627370496) r3))) (let ((.def_160 (* (- (/ 4312467424539675 4503599627370496)) r2))) (let ((.def_161 (* (- (/ 333523766005929 4503599627370496)) r1))) (let ((.def_162 (* (- (/ 2314315736402359 2251799813685248)) r0))) (let ((.def_163 (+ .def_162 .def_161 .def_160 .def_159))) (let ((.def_164 (<= .def_163 (- (/ 616914129739783 2251799813685248))))) (let ((.def_165 (* (- (/ 757904675159899 9007199254740992)) r3))) (let ((.def_166 (* (/ 2955959301751567 9007199254740992) r2))) (let ((.def_167 (* (- (/ 5396721514063527 2251799813685248)) r1))) (let ((.def_168 (* (- (/ 1226351374209591 9007199254740992)) r0))) (let ((.def_169 (+ .def_168 .def_167 .def_166 .def_165))) (let ((.def_170 (<= .def_169 (- (/ 5488086686333471 4503599627370496))))) (let ((.def_171 (or .def_131 .def_170 .def_164))) (let ((.def_172 (* (- (/ 680354292243375 281474976710656)) r3))) (let ((.def_173 (* (/ 1939014231302533 1125899906842624) r2))) (let ((.def_174 (* (/ 1871425713822027 4503599627370496) r1))) (let ((.def_175 (* (- (/ 4127487997311267 4503599627370496)) r0))) (let ((.def_176 (+ .def_175 .def_174 .def_173 .def_172))) (let ((.def_177 (<= .def_176 (/ 5417609176729633 9007199254740992)))) (let ((.def_178 (* (- (/ 1704223122409525 2251799813685248)) r3))) (let ((.def_179 (* (/ 666315384070511 562949953421312) r2))) (let ((.def_180 (* (/ 160320091797881 1125899906842624) r1))) (let ((.def_181 (* (- (/ 11173745064255 2251799813685248)) r0))) (let ((.def_182 (+ .def_181 .def_180 .def_179 .def_178))) (let ((.def_183 (<= .def_182 (/ 1138561965949813 4503599627370496)))) (let ((.def_184 (or b2 .def_183 .def_177))) (let ((.def_185 (* (- (/ 5790160819558121 9007199254740992)) r3))) (let ((.def_186 (* (- (/ 2269796922740513 1125899906842624)) r2))) (let ((.def_187 (* (- (/ 989214818498349 4503599627370496)) r1))) (let ((.def_188 (* (/ 309590791888365 562949953421312) r0))) (let ((.def_189 (+ .def_188 .def_187 .def_186 .def_185))) (let ((.def_190 (<= .def_189 (- (/ 1895825423560305 9007199254740992))))) (let ((.def_191 (* (/ 3350149964988407 9007199254740992) r3))) (let ((.def_192 (* (- (/ 4714178782442705 4503599627370496)) r2))) (let ((.def_193 (* (/ 2564244877762887 2251799813685248) r1))) (let ((.def_194 (* (/ 619554768901477 4503599627370496) r0))) (let ((.def_195 (+ .def_194 .def_193 .def_192 .def_191))) (let ((.def_196 (<= .def_195 (/ 2078402776011757 9007199254740992)))) (let ((.def_197 (or .def_51 .def_196 .def_190))) (let ((.def_198 (* (/ 2605441885167939 4503599627370496) r3))) (let ((.def_199 (* (- (/ 1960551360323633 9007199254740992)) r2))) (let ((.def_200 (* (/ 585094146011013 9007199254740992) r1))) (let ((.def_201 (* (- (/ 7272065544086301 9007199254740992)) r0))) (let ((.def_202 (+ .def_201 .def_200 .def_199 .def_198))) (let ((.def_203 (<= .def_202 (/ 525638920779093 4503599627370496)))) (let ((.def_204 (* (- (/ 3832759134723353 9007199254740992)) r3))) (let ((.def_205 (* (- (/ 46666595639383 2251799813685248)) r2))) (let ((.def_206 (* (/ 7711799675091547 2251799813685248) r1))) (let ((.def_207 (* (- (/ 5429636977930927 9007199254740992)) r0))) (let ((.def_208 (+ .def_207 .def_206 .def_205 .def_204))) (let ((.def_209 (<= .def_208 (/ 1012664606996015 1125899906842624)))) (let ((.def_210 (or b1 .def_209 .def_203))) (let ((.def_211 (* (- (/ 2817487210252179 4503599627370496)) r3))) (let ((.def_212 (* (/ 9420188696327 281474976710656) r2))) (let ((.def_213 (* (/ 4671694517696731 9007199254740992) r1))) (let ((.def_214 (* (- (/ 3894989805733075 4503599627370496)) r0))) (let ((.def_215 (+ .def_214 .def_213 .def_212 .def_211))) (let ((.def_216 (<= .def_215 (- (/ 265748387936239 4503599627370496))))) (let ((.def_217 (* (/ 157814674483335 562949953421312) r3))) (let ((.def_218 (* (/ 1964539399069781 2251799813685248) r2))) (let ((.def_219 (* (/ 2477580217319571 2251799813685248) r1))) (let ((.def_220 (* (/ 3660250592228963 4503599627370496) r0))) (let ((.def_221 (+ .def_220 .def_219 .def_218 .def_217))) (let ((.def_222 (<= .def_221 (/ 422005677735005 281474976710656)))) (let ((.def_223 (or b0 .def_222 .def_216))) (let ((.def_224 (* (/ 1792361262513833 1125899906842624) r3))) (let ((.def_225 (* (- (/ 3138220295467663 1125899906842624)) r2))) (let ((.def_226 (* (/ 995706632617843 4503599627370496) r1))) (let ((.def_227 (* (- (/ 4268644535473865 2251799813685248)) r0))) (let ((.def_228 (+ .def_227 .def_226 .def_225 .def_224))) (let ((.def_229 (<= .def_228 (/ 2166963915144357 9007199254740992)))) (let ((.def_230 (* (/ 557662207907487 562949953421312) r3))) (let ((.def_231 (* (- (/ 7457694035476253 9007199254740992)) r2))) (let ((.def_232 (* (/ 575081865973921 4503599627370496) r1))) (let ((.def_233 (* (/ 1660493022227285 9007199254740992) r0))) (let ((.def_234 (+ .def_233 .def_232 .def_231 .def_230))) (let ((.def_235 (<= .def_234 (/ 501631126308629 2251799813685248)))) (let ((.def_236 (not b3))) (let ((.def_237 (or .def_236 .def_235 .def_229))) (let ((.def_238 (* (- (/ 108843821131699 281474976710656)) r3))) (let ((.def_239 (* (- (/ 1023945620648393 1125899906842624)) r2))) (let ((.def_240 (* (/ 290040098115679 562949953421312) r1))) (let ((.def_241 (* (- (/ 1640002623329465 2251799813685248)) r0))) (let ((.def_242 (+ .def_241 .def_240 .def_239 .def_238))) (let ((.def_243 (<= .def_242 (- (/ 848916603546463 2251799813685248))))) (let ((.def_244 (* (- (/ 1603058312375413 4503599627370496)) r3))) (let ((.def_245 (* (/ 6886220347814453 4503599627370496) r2))) (let ((.def_246 (* (- (/ 5109113068377169 9007199254740992)) r1))) (let ((.def_247 (* (- (/ 4546899225693013 9007199254740992)) r0))) (let ((.def_248 (+ .def_247 .def_246 .def_245 .def_244))) (let ((.def_249 (<= .def_248 (- (/ 91381653795779 4503599627370496))))) (let ((.def_250 (or b2 .def_249 .def_243))) (let ((.def_251 (and .def_250 .def_237 .def_223 .def_210 .def_197 .def_184 .def_171 .def_158 .def_145 .def_132 .def_118 .def_105 .def_91 .def_78 .def_65 .def_52 .def_38 .def_25 .def_12))) .def_251)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)