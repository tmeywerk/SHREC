(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun b3 () Bool)
(declare-fun r0 () Real)
(declare-fun b0 () Bool)
(declare-fun r1 () Real)
(declare-fun b2 () Bool)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (- (/ 104859707559089 2251799813685248)) r3))) (let ((.def_1 (* (- (/ 6444938720668341 9007199254740992)) r2))) (let ((.def_2 (* (- (/ 1412185381326473 2251799813685248)) r1))) (let ((.def_3 (* (/ 532296134029631 562949953421312) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 1018261396863933 4503599627370496)))) (let ((.def_6 (* (/ 2718619682125915 4503599627370496) r3))) (let ((.def_7 (* (/ 3099453178589025 4503599627370496) r2))) (let ((.def_8 (* (- (/ 3733329777786373 4503599627370496)) r1))) (let ((.def_9 (* (/ 1311379445021785 1125899906842624) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 3483231513056403 4503599627370496)))) (let ((.def_12 (not b0))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (/ 849918194962407 4503599627370496) r3))) (let ((.def_15 (* (- (/ 5327229615099227 9007199254740992)) r2))) (let ((.def_16 (* (- (/ 676711387239697 2251799813685248)) r1))) (let ((.def_17 (* (- (/ 2075571708896329 4503599627370496)) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 1424598644305421 4503599627370496))))) (let ((.def_20 (* (/ 8782140865707443 9007199254740992) r3))) (let ((.def_21 (* (- (/ 1918430233461531 2251799813685248)) r2))) (let ((.def_22 (* (/ 4183609310988873 4503599627370496) r1))) (let ((.def_23 (* (- (/ 2813876976330051 2251799813685248)) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (- (/ 2349322699145721 9007199254740992))))) (let ((.def_26 (or b2 .def_25 .def_19))) (let ((.def_27 (* (/ 1032222225382957 1125899906842624) r3))) (let ((.def_28 (* (/ 4998634729731419 9007199254740992) r2))) (let ((.def_29 (* (- (/ 3890523534139433 9007199254740992)) r1))) (let ((.def_30 (* (/ 939073949127853 2251799813685248) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 1508283611071815 1125899906842624)))) (let ((.def_33 (* (/ 601795452140677 4503599627370496) r3))) (let ((.def_34 (* (/ 978720146420093 1125899906842624) r2))) (let ((.def_35 (* (- (/ 3026779194425579 2251799813685248)) r1))) (let ((.def_36 (* (/ 82100801769753 140737488355328) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (/ 548276932056313 9007199254740992)))) (let ((.def_39 (or b0 .def_38 .def_32))) (let ((.def_40 (* (/ 111278783776411 2251799813685248) r3))) (let ((.def_41 (* (/ 4177687129009261 9007199254740992) r2))) (let ((.def_42 (* (/ 1701221192092465 4503599627370496) r1))) (let ((.def_43 (* (- (/ 4518624508279827 9007199254740992)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (/ 2469149410945619 9007199254740992)))) (let ((.def_46 (* (/ 3304277185999011 9007199254740992) r3))) (let ((.def_47 (* (- (/ 6854198386685291 4503599627370496)) r2))) (let ((.def_48 (* (/ 3191866619685137 9007199254740992) r1))) (let ((.def_49 (* (/ 4536776579741325 9007199254740992) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 257546630277923 1125899906842624))))) (let ((.def_52 (or b1 .def_51 .def_45))) (let ((.def_53 (* (- (/ 1391421342379505 4503599627370496)) r3))) (let ((.def_54 (* (- (/ 1726364394247417 4503599627370496)) r2))) (let ((.def_55 (* (/ 1946641357341211 2251799813685248) r1))) (let ((.def_56 (* (/ 406485862230519 1125899906842624) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 163985552028417 281474976710656)))) (let ((.def_59 (* (/ 1811988676212339 9007199254740992) r3))) (let ((.def_60 (* (- (/ 671107973814405 1125899906842624)) r2))) (let ((.def_61 (* (- (/ 1642643978181561 2251799813685248)) r1))) (let ((.def_62 (* (/ 514121126841441 562949953421312) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (- (/ 1952669033040227 9007199254740992))))) (let ((.def_65 (or b2 .def_64 .def_58))) (let ((.def_66 (* (/ 6632588138782563 2251799813685248) r3))) (let ((.def_67 (* (/ 1022650040310383 9007199254740992) r2))) (let ((.def_68 (* (- (/ 536725766456995 281474976710656)) r1))) (let ((.def_69 (* (- (/ 4251697027771897 2251799813685248)) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (/ 1249473503171059 2251799813685248)))) (let ((.def_72 (* (- (/ 1243056263009627 1125899906842624)) r3))) (let ((.def_73 (* (- (/ 5847616883020501 4503599627370496)) r2))) (let ((.def_74 (* (/ 4631276015938033 2251799813685248) r1))) (let ((.def_75 (* (- (/ 5875891313655067 4503599627370496)) r0))) (let ((.def_76 (+ .def_75 .def_74 .def_73 .def_72))) (let ((.def_77 (<= .def_76 (- (/ 6999443470950439 9007199254740992))))) (let ((.def_78 (not b3))) (let ((.def_79 (or .def_78 .def_77 .def_71))) (let ((.def_80 (* (/ 2998576177244747 2251799813685248) r3))) (let ((.def_81 (* (- (/ 74364370007323 70368744177664)) r2))) (let ((.def_82 (* (- (/ 499904756859471 2251799813685248)) r1))) (let ((.def_83 (* (/ 2211071726722381 9007199254740992) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 3946030312701993 4503599627370496)))) (let ((.def_86 (* (/ 2644710161545617 1125899906842624) r3))) (let ((.def_87 (* (- (/ 3653368038126637 9007199254740992)) r2))) (let ((.def_88 (* (- (/ 2276169181591497 2251799813685248)) r1))) (let ((.def_89 (* (/ 2983706297749009 4503599627370496) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (/ 6933140740232235 9007199254740992)))) (let ((.def_92 (not b1))) (let ((.def_93 (or .def_92 .def_91 .def_85))) (let ((.def_94 (* (- (/ 868415797320389 4503599627370496)) r3))) (let ((.def_95 (* (- (/ 381482920132703 1125899906842624)) r2))) (let ((.def_96 (* (- (/ 1197879855182869 1125899906842624)) r1))) (let ((.def_97 (* (- (/ 2816380692212667 4503599627370496)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (- (/ 770478622990041 1125899906842624))))) (let ((.def_100 (* (/ 1499526215030927 1125899906842624) r3))) (let ((.def_101 (* (- (/ 7061716583159047 2251799813685248)) r2))) (let ((.def_102 (* (- (/ 1114689105550393 9007199254740992)) r1))) (let ((.def_103 (* (/ 2522682624561777 2251799813685248) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (- (/ 4139701000342973 9007199254740992))))) (let ((.def_106 (or b0 .def_105 .def_99))) (let ((.def_107 (* (/ 507580390432719 1125899906842624) r3))) (let ((.def_108 (* (- (/ 607902088604093 2251799813685248)) r2))) (let ((.def_109 (* (- (/ 177215296408003 281474976710656)) r1))) (let ((.def_110 (* (- (/ 888244950357793 1125899906842624)) r0))) (let ((.def_111 (+ .def_110 .def_109 .def_108 .def_107))) (let ((.def_112 (<= .def_111 (- (/ 2595570710813965 9007199254740992))))) (let ((.def_113 (* (/ 4487630070390847 4503599627370496) r3))) (let ((.def_114 (* (/ 6541634750833873 2251799813685248) r2))) (let ((.def_115 (* (- (/ 15288599929089 140737488355328)) r1))) (let ((.def_116 (* (/ 2473854147011415 9007199254740992) r0))) (let ((.def_117 (+ .def_116 .def_115 .def_114 .def_113))) (let ((.def_118 (<= .def_117 (/ 2272348894750139 1125899906842624)))) (let ((.def_119 (or .def_92 .def_118 .def_112))) (let ((.def_120 (* (- (/ 737305028690227 1125899906842624)) r3))) (let ((.def_121 (* (/ 479177938137661 4503599627370496) r2))) (let ((.def_122 (* (- (/ 4968540223961849 9007199254740992)) r1))) (let ((.def_123 (* (/ 3258767986975355 4503599627370496) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (/ 1730142389316701 9007199254740992)))) (let ((.def_126 (* (/ 2589686912798571 9007199254740992) r3))) (let ((.def_127 (* (- (/ 467169434942561 9007199254740992)) r2))) (let ((.def_128 (* (- (/ 8096444382832459 9007199254740992)) r1))) (let ((.def_129 (* (- (/ 6695405902420443 9007199254740992)) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (- (/ 3235929871220767 4503599627370496))))) (let ((.def_132 (or b2 .def_131 .def_125))) (let ((.def_133 (* (- (/ 1437173433873331 2251799813685248)) r3))) (let ((.def_134 (* (/ 88267627970157 2251799813685248) r2))) (let ((.def_135 (* (- (/ 2931627369025 4503599627370496)) r1))) (let ((.def_136 (* (- (/ 2369047285635123 2251799813685248)) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 2103438006694491 9007199254740992))))) (let ((.def_139 (* (/ 597827013994477 4503599627370496) r3))) (let ((.def_140 (* (/ 6754874446209391 9007199254740992) r2))) (let ((.def_141 (* (/ 3806530132958107 2251799813685248) r1))) (let ((.def_142 (* (- (/ 66472961640415 4503599627370496)) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (/ 2802771345705739 2251799813685248)))) (let ((.def_145 (or .def_78 .def_144 .def_138))) (let ((.def_146 (* (/ 3388379961837575 4503599627370496) r3))) (let ((.def_147 (* (- (/ 927922423549419 4503599627370496)) r2))) (let ((.def_148 (* (/ 1928608159837503 4503599627370496) r1))) (let ((.def_149 (* (- (/ 70524694089735 1125899906842624)) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 1891305897992237 2251799813685248)))) (let ((.def_152 (* (/ 512649107422755 4503599627370496) r3))) (let ((.def_153 (* (/ 291986862558109 9007199254740992) r2))) (let ((.def_154 (* (- (/ 832790799096503 9007199254740992)) r1))) (let ((.def_155 (* (/ 5669349721538293 9007199254740992) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (/ 791168592493303 2251799813685248)))) (let ((.def_158 (or b0 .def_157 .def_151))) (let ((.def_159 (* (- (/ 1691775429045399 2251799813685248)) r3))) (let ((.def_160 (* (- (/ 554948461596737 562949953421312)) r2))) (let ((.def_161 (* (/ 4146935447212393 4503599627370496) r1))) (let ((.def_162 (* (/ 45286832850439 1125899906842624) r0))) (let ((.def_163 (+ .def_162 .def_161 .def_160 .def_159))) (let ((.def_164 (<= .def_163 (/ 872863127235463 4503599627370496)))) (let ((.def_165 (* (- (/ 256170959229411 9007199254740992)) r3))) (let ((.def_166 (* (- (/ 8142204643124669 9007199254740992)) r2))) (let ((.def_167 (* (- (/ 194606014853737 1125899906842624)) r1))) (let ((.def_168 (* (/ 8671215161825423 9007199254740992) r0))) (let ((.def_169 (+ .def_168 .def_167 .def_166 .def_165))) (let ((.def_170 (<= .def_169 (- (/ 444118529654829 9007199254740992))))) (let ((.def_171 (not b2))) (let ((.def_172 (or .def_171 .def_170 .def_164))) (let ((.def_173 (* (/ 48093613565199 70368744177664) r3))) (let ((.def_174 (* (- (/ 3482666125878333 4503599627370496)) r2))) (let ((.def_175 (* (/ 1164525187751809 2251799813685248) r1))) (let ((.def_176 (* (/ 2169159855165287 4503599627370496) r0))) (let ((.def_177 (+ .def_176 .def_175 .def_174 .def_173))) (let ((.def_178 (<= .def_177 (/ 1601314966677333 2251799813685248)))) (let ((.def_179 (* (- (/ 326048697829363 140737488355328)) r3))) (let ((.def_180 (* (- (/ 213513791755585 2251799813685248)) r2))) (let ((.def_181 (* (- (/ 784794743654621 9007199254740992)) r1))) (let ((.def_182 (* (- (/ 8807806538741955 9007199254740992)) r0))) (let ((.def_183 (+ .def_182 .def_181 .def_180 .def_179))) (let ((.def_184 (<= .def_183 (- (/ 4081344210216059 2251799813685248))))) (let ((.def_185 (or .def_12 .def_184 .def_178))) (let ((.def_186 (* (/ 5859405777460327 9007199254740992) r3))) (let ((.def_187 (* (/ 2517405228198353 9007199254740992) r2))) (let ((.def_188 (* (- (/ 3384406210467355 9007199254740992)) r1))) (let ((.def_189 (* (- (/ 3951355856251785 9007199254740992)) r0))) (let ((.def_190 (+ .def_189 .def_188 .def_187 .def_186))) (let ((.def_191 (<= .def_190 (/ 439954705776037 1125899906842624)))) (let ((.def_192 (* (- (/ 3426581423146475 9007199254740992)) r3))) (let ((.def_193 (* (- (/ 248502250325565 140737488355328)) r2))) (let ((.def_194 (* (- (/ 4337155573366781 1125899906842624)) r1))) (let ((.def_195 (* (/ 3735780717602587 2251799813685248) r0))) (let ((.def_196 (+ .def_195 .def_194 .def_193 .def_192))) (let ((.def_197 (<= .def_196 (- (/ 5071215515686355 2251799813685248))))) (let ((.def_198 (or b1 .def_197 .def_191))) (let ((.def_199 (* (/ 690382242910951 9007199254740992) r3))) (let ((.def_200 (* (/ 5019101531189323 9007199254740992) r2))) (let ((.def_201 (* (- (/ 1949171365519003 4503599627370496)) r1))) (let ((.def_202 (* (- (/ 3092773760778369 2251799813685248)) r0))) (let ((.def_203 (+ .def_202 .def_201 .def_200 .def_199))) (let ((.def_204 (<= .def_203 (/ 88203985880395 1125899906842624)))) (let ((.def_205 (* (- (/ 3389246226409407 2251799813685248)) r3))) (let ((.def_206 (* (/ 2488023326582353 4503599627370496) r2))) (let ((.def_207 (* (/ 1376692453087713 4503599627370496) r1))) (let ((.def_208 (* (- (/ 5081286077277999 9007199254740992)) r0))) (let ((.def_209 (+ .def_208 .def_207 .def_206 .def_205))) (let ((.def_210 (<= .def_209 (- (/ 6226492764380307 9007199254740992))))) (let ((.def_211 (or b3 .def_210 .def_204))) (let ((.def_212 (* (- (/ 809514977635951 562949953421312)) r3))) (let ((.def_213 (* (- (/ 2317787307914793 4503599627370496)) r2))) (let ((.def_214 (* (/ 1973251215757451 2251799813685248) r1))) (let ((.def_215 (* (- (/ 2389334221838139 4503599627370496)) r0))) (let ((.def_216 (+ .def_215 .def_214 .def_213 .def_212))) (let ((.def_217 (<= .def_216 (- (/ 6192537932343201 9007199254740992))))) (let ((.def_218 (* (/ 1428914320718953 1125899906842624) r3))) (let ((.def_219 (* (/ 8197267647338719 9007199254740992) r2))) (let ((.def_220 (* (- (/ 611494118341403 281474976710656)) r1))) (let ((.def_221 (* (- (/ 312108555293095 2251799813685248)) r0))) (let ((.def_222 (+ .def_221 .def_220 .def_219 .def_218))) (let ((.def_223 (<= .def_222 (- (/ 577193056701907 4503599627370496))))) (let ((.def_224 (or b0 .def_223 .def_217))) (let ((.def_225 (* (- (/ 4155789297957637 4503599627370496)) r3))) (let ((.def_226 (* (/ 136806001193543 281474976710656) r2))) (let ((.def_227 (* (- (/ 2010464721513065 4503599627370496)) r1))) (let ((.def_228 (* (- (/ 71665635462555 1125899906842624)) r0))) (let ((.def_229 (+ .def_228 .def_227 .def_226 .def_225))) (let ((.def_230 (<= .def_229 (- (/ 436676442046471 2251799813685248))))) (let ((.def_231 (* (/ 2251997149076625 4503599627370496) r3))) (let ((.def_232 (* (- (/ 8212501122745479 9007199254740992)) r2))) (let ((.def_233 (* (/ 45566653436775 140737488355328) r1))) (let ((.def_234 (* (/ 2216541089703513 2251799813685248) r0))) (let ((.def_235 (+ .def_234 .def_233 .def_232 .def_231))) (let ((.def_236 (<= .def_235 (/ 895825788006357 2251799813685248)))) (let ((.def_237 (or .def_12 .def_236 .def_230))) (let ((.def_238 (* (- (/ 1100167310348239 2251799813685248)) r3))) (let ((.def_239 (* (- (/ 259860479146397 1125899906842624)) r2))) (let ((.def_240 (* (- (/ 626809005487903 2251799813685248)) r1))) (let ((.def_241 (* (/ 173284655855607 1125899906842624) r0))) (let ((.def_242 (+ .def_241 .def_240 .def_239 .def_238))) (let ((.def_243 (<= .def_242 (- (/ 1126445894795187 4503599627370496))))) (let ((.def_244 (* (/ 4980721053534055 2251799813685248) r3))) (let ((.def_245 (* (- (/ 6415133074753389 9007199254740992)) r2))) (let ((.def_246 (* (- (/ 3747939461967859 9007199254740992)) r1))) (let ((.def_247 (* (/ 7810102987818379 9007199254740992) r0))) (let ((.def_248 (+ .def_247 .def_246 .def_245 .def_244))) (let ((.def_249 (<= .def_248 (/ 4137518506559137 4503599627370496)))) (let ((.def_250 (or .def_12 .def_249 .def_243))) (let ((.def_251 (* (- (/ 2010693089611643 2251799813685248)) r3))) (let ((.def_252 (* (- (/ 4842503114575623 4503599627370496)) r2))) (let ((.def_253 (* (- (/ 1041863486424139 1125899906842624)) r1))) (let ((.def_254 (* (/ 2485209616300185 1125899906842624) r0))) (let ((.def_255 (+ .def_254 .def_253 .def_252 .def_251))) (let ((.def_256 (<= .def_255 (/ 756899310922849 1125899906842624)))) (let ((.def_257 (* (- (/ 5203944180083323 4503599627370496)) r3))) (let ((.def_258 (* (/ 601505958606069 562949953421312) r2))) (let ((.def_259 (* (/ 1101793262923241 4503599627370496) r1))) (let ((.def_260 (* (- (/ 995448091077015 9007199254740992)) r0))) (let ((.def_261 (+ .def_260 .def_259 .def_258 .def_257))) (let ((.def_262 (<= .def_261 (/ 1983808298335 4503599627370496)))) (let ((.def_263 (or b0 .def_262 .def_256))) (let ((.def_264 (* (- (/ 828016939108271 562949953421312)) r3))) (let ((.def_265 (* (/ 606821676135585 562949953421312) r2))) (let ((.def_266 (* (- (/ 8240260048361385 4503599627370496)) r1))) (let ((.def_267 (* (- (/ 2174214611587719 1125899906842624)) r0))) (let ((.def_268 (+ .def_267 .def_266 .def_265 .def_264))) (let ((.def_269 (<= .def_268 (- (/ 2749948988066763 4503599627370496))))) (let ((.def_270 (* (- (/ 2232057569601953 2251799813685248)) r3))) (let ((.def_271 (* (/ 458080054228085 281474976710656) r2))) (let ((.def_272 (* (- (/ 1024115565597903 9007199254740992)) r1))) (let ((.def_273 (* (- (/ 3598056306313873 2251799813685248)) r0))) (let ((.def_274 (+ .def_273 .def_272 .def_271 .def_270))) (let ((.def_275 (<= .def_274 (- (/ 1334726019994823 2251799813685248))))) (let ((.def_276 (or b0 .def_275 .def_269))) (let ((.def_277 (and .def_276 .def_263 .def_250 .def_237 .def_224 .def_211 .def_198 .def_185 .def_172 .def_158 .def_145 .def_132 .def_119 .def_106 .def_93 .def_79 .def_65 .def_52 .def_39 .def_26 .def_13))) .def_277)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
