(set-logic QF_LRA)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b3 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(assert (let ((.def_0 (* (- (/ 2557262447544475 1125899906842624)) r3))) (let ((.def_1 (* (/ 3379323898125109 4503599627370496) r2))) (let ((.def_2 (* (- (/ 1211264201873891 2251799813685248)) r1))) (let ((.def_3 (* (/ 101539195914147 4503599627370496) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1964698686486841 9007199254740992))))) (let ((.def_6 (* (- (/ 8958987472667143 4503599627370496)) r3))) (let ((.def_7 (* (- (/ 1267690312108827 562949953421312)) r2))) (let ((.def_8 (* (/ 244728424823865 140737488355328) r1))) (let ((.def_9 (* (/ 2808252882185929 9007199254740992) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 295462973582125 281474976710656))))) (let ((.def_12 (not b1))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 1288843624777591 2251799813685248)) r3))) (let ((.def_15 (* (/ 3611688096966637 4503599627370496) r2))) (let ((.def_16 (* (/ 6378161605802763 4503599627370496) r1))) (let ((.def_17 (* (/ 3906734752537901 4503599627370496) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (/ 1065637192049899 562949953421312)))) (let ((.def_20 (* (- (/ 3060774295661957 4503599627370496)) r3))) (let ((.def_21 (* (- (/ 967452805068119 2251799813685248)) r2))) (let ((.def_22 (* (/ 7706707834548685 9007199254740992) r1))) (let ((.def_23 (* (- (/ 1638619593476145 2251799813685248)) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (- (/ 4985007673683801 9007199254740992))))) (let ((.def_26 (or b1 .def_25 .def_19))) (let ((.def_27 (* (/ 2185067033483087 2251799813685248) r3))) (let ((.def_28 (* (/ 4294528155673101 2251799813685248) r2))) (let ((.def_29 (* (/ 1085918312614581 1125899906842624) r1))) (let ((.def_30 (* (- (/ 1409494682593633 1125899906842624)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 1232040667269851 562949953421312)))) (let ((.def_33 (* (- (/ 1001115155037473 4503599627370496)) r3))) (let ((.def_34 (* (/ 1210977829625539 1125899906842624) r2))) (let ((.def_35 (* (/ 3705083079161741 4503599627370496) r1))) (let ((.def_36 (* (- (/ 4835518436180583 9007199254740992)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (/ 5417483110699479 9007199254740992)))) (let ((.def_39 (not b3))) (let ((.def_40 (or .def_39 .def_38 .def_32))) (let ((.def_41 (* (- (/ 4166406739425391 4503599627370496)) r3))) (let ((.def_42 (* (- (/ 271249839245137 281474976710656)) r2))) (let ((.def_43 (* (- (/ 2248330947913253 2251799813685248)) r1))) (let ((.def_44 (* (/ 32727119028455 35184372088832) r0))) (let ((.def_45 (+ .def_44 .def_43 .def_42 .def_41))) (let ((.def_46 (<= .def_45 (- (/ 521619202287593 1125899906842624))))) (let ((.def_47 (* (- (/ 8614998058924335 9007199254740992)) r3))) (let ((.def_48 (* (/ 1617535628164591 9007199254740992) r2))) (let ((.def_49 (* (/ 1325517539839753 4503599627370496) r1))) (let ((.def_50 (* (/ 884496570319697 9007199254740992) r0))) (let ((.def_51 (+ .def_50 .def_49 .def_48 .def_47))) (let ((.def_52 (<= .def_51 (- (/ 1837005021291099 9007199254740992))))) (let ((.def_53 (or .def_39 .def_52 .def_46))) (let ((.def_54 (* (/ 1187564794206529 4503599627370496) r3))) (let ((.def_55 (* (/ 3217321468633281 4503599627370496) r2))) (let ((.def_56 (* (- (/ 7953478000484407 4503599627370496)) r1))) (let ((.def_57 (* (- (/ 334619911822457 4503599627370496)) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (- (/ 2669305168116601 9007199254740992))))) (let ((.def_60 (* (/ 3375254785521777 4503599627370496) r3))) (let ((.def_61 (* (- (/ 2204460441112217 4503599627370496)) r2))) (let ((.def_62 (* (/ 5854625920635905 4503599627370496) r1))) (let ((.def_63 (* (- (/ 1145271283896661 2251799813685248)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 5187914971960735 9007199254740992)))) (let ((.def_66 (or .def_12 .def_65 .def_59))) (let ((.def_67 (* (/ 2359114858639161 4503599627370496) r3))) (let ((.def_68 (* (/ 4207473634754465 4503599627370496) r2))) (let ((.def_69 (* (- (/ 7165751254104857 9007199254740992)) r1))) (let ((.def_70 (* (/ 2838278912520721 2251799813685248) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 3313050797385409 2251799813685248)))) (let ((.def_73 (* (/ 1103938065665191 1125899906842624) r3))) (let ((.def_74 (* (- (/ 825175470616407 2251799813685248)) r2))) (let ((.def_75 (* (- (/ 107330367297639 70368744177664)) r1))) (let ((.def_76 (* (- (/ 2871073898538643 2251799813685248)) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 2829440029465155 2251799813685248))))) (let ((.def_79 (or b0 .def_78 .def_72))) (let ((.def_80 (* (- (/ 3277415077417119 4503599627370496)) r3))) (let ((.def_81 (* (/ 1034340469651255 1125899906842624) r2))) (let ((.def_82 (* (/ 1011872589881105 1125899906842624) r1))) (let ((.def_83 (* (- (/ 1853906518489527 2251799813685248)) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 4939319933000075 9007199254740992)))) (let ((.def_86 (* (/ 1725847400859395 2251799813685248) r3))) (let ((.def_87 (* (/ 77375108844291 140737488355328) r2))) (let ((.def_88 (* (- (/ 2511880655427169 4503599627370496)) r1))) (let ((.def_89 (* (- (/ 1274374926599031 9007199254740992)) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (/ 1424220554441405 4503599627370496)))) (let ((.def_92 (or .def_39 .def_91 .def_85))) (let ((.def_93 (* (/ 4984793350509439 9007199254740992) r3))) (let ((.def_94 (* (- (/ 2763149646557495 1125899906842624)) r2))) (let ((.def_95 (* (- (/ 5704424683786647 4503599627370496)) r1))) (let ((.def_96 (* (- (/ 554388816172493 2251799813685248)) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (- (/ 6110695730291605 9007199254740992))))) (let ((.def_99 (* (/ 10849196607725 4398046511104) r3))) (let ((.def_100 (* (- (/ 4826428047790975 9007199254740992)) r2))) (let ((.def_101 (* (- (/ 903274586110863 562949953421312)) r1))) (let ((.def_102 (* (- (/ 834171094448035 9007199254740992)) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (/ 753344363124421 4503599627370496)))) (let ((.def_105 (or b0 .def_104 .def_98))) (let ((.def_106 (* (/ 688611022303323 9007199254740992) r3))) (let ((.def_107 (* (- (/ 2309604423872215 2251799813685248)) r2))) (let ((.def_108 (* (- (/ 3369539952208421 2251799813685248)) r1))) (let ((.def_109 (* (/ 4944678175164875 4503599627370496) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (/ 249591050528639 4503599627370496)))) (let ((.def_112 (* (/ 2315716200131229 9007199254740992) r3))) (let ((.def_113 (* (- (/ 3278240992542111 9007199254740992)) r2))) (let ((.def_114 (* (- (/ 1103371588930045 562949953421312)) r1))) (let ((.def_115 (* (/ 2031389728414953 2251799813685248) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (- (/ 1608331404149703 2251799813685248))))) (let ((.def_118 (or .def_12 .def_117 .def_111))) (let ((.def_119 (* (- (/ 1196027892157801 1125899906842624)) r3))) (let ((.def_120 (* (- (/ 1341210575321647 9007199254740992)) r2))) (let ((.def_121 (* (/ 1254451718481053 2251799813685248) r1))) (let ((.def_122 (* (- (/ 2880878991422607 4503599627370496)) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (- (/ 197977715117 1125899906842624))))) (let ((.def_125 (* (- (/ 3228877651841783 4503599627370496)) r3))) (let ((.def_126 (* (- (/ 1541787044349371 9007199254740992)) r2))) (let ((.def_127 (* (/ 958580148728859 4503599627370496) r1))) (let ((.def_128 (* (- (/ 606763207799125 2251799813685248)) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (- (/ 554329722818025 1125899906842624))))) (let ((.def_131 (not b2))) (let ((.def_132 (or .def_131 .def_130 .def_124))) (let ((.def_133 (* (- (/ 1785054139481907 9007199254740992)) r3))) (let ((.def_134 (* (- (/ 424109186346509 281474976710656)) r2))) (let ((.def_135 (* (- (/ 2722036531004467 2251799813685248)) r1))) (let ((.def_136 (* (/ 1446049596603211 1125899906842624) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (/ 772417827417755 9007199254740992)))) (let ((.def_139 (* (/ 3186841424790375 9007199254740992) r3))) (let ((.def_140 (* (- (/ 4340031252046237 2251799813685248)) r2))) (let ((.def_141 (* (/ 5514970106870367 9007199254740992) r1))) (let ((.def_142 (* (/ 1431575091752697 9007199254740992) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (- (/ 1718793327942395 4503599627370496))))) (let ((.def_145 (or .def_39 .def_144 .def_138))) (let ((.def_146 (* (/ 389354891338109 2251799813685248) r3))) (let ((.def_147 (* (/ 2124564901375785 9007199254740992) r2))) (let ((.def_148 (* (- (/ 3756250793469927 9007199254740992)) r1))) (let ((.def_149 (* (/ 3985640603671689 4503599627370496) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 7685540200619897 9007199254740992)))) (let ((.def_152 (* (/ 2881325194355303 2251799813685248) r3))) (let ((.def_153 (* (- (/ 1751683675733663 9007199254740992)) r2))) (let ((.def_154 (* (/ 577334795432999 2251799813685248) r1))) (let ((.def_155 (* (/ 2575924417039067 1125899906842624) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (/ 7788235523015051 4503599627370496)))) (let ((.def_158 (not b0))) (let ((.def_159 (or .def_158 .def_157 .def_151))) (let ((.def_160 (* (/ 465601791089857 4503599627370496) r3))) (let ((.def_161 (* (- (/ 45135439209981 2251799813685248)) r2))) (let ((.def_162 (* (- (/ 544554200640935 562949953421312)) r1))) (let ((.def_163 (* (/ 3300294158115953 2251799813685248) r0))) (let ((.def_164 (+ .def_163 .def_162 .def_161 .def_160))) (let ((.def_165 (<= .def_164 (/ 1629101151494929 2251799813685248)))) (let ((.def_166 (* (- (/ 5757657048657559 2251799813685248)) r3))) (let ((.def_167 (* (- (/ 847322535497789 9007199254740992)) r2))) (let ((.def_168 (* (- (/ 1117915893415297 9007199254740992)) r1))) (let ((.def_169 (* (/ 352226412017797 9007199254740992) r0))) (let ((.def_170 (+ .def_169 .def_168 .def_167 .def_166))) (let ((.def_171 (<= .def_170 (- (/ 3335547866055765 2251799813685248))))) (let ((.def_172 (or .def_158 .def_171 .def_165))) (let ((.def_173 (* (- (/ 712632914906197 9007199254740992)) r3))) (let ((.def_174 (* (/ 1715270021048603 2251799813685248) r2))) (let ((.def_175 (* (- (/ 2351380242338817 2251799813685248)) r1))) (let ((.def_176 (* (- (/ 2603234002345209 2251799813685248)) r0))) (let ((.def_177 (+ .def_176 .def_175 .def_174 .def_173))) (let ((.def_178 (<= .def_177 (- (/ 1007978646675943 2251799813685248))))) (let ((.def_179 (* (- (/ 4826402621587463 2251799813685248)) r3))) (let ((.def_180 (* (/ 568849894652903 562949953421312) r2))) (let ((.def_181 (* (/ 1406981947469153 4503599627370496) r1))) (let ((.def_182 (* (/ 2553158321945349 1125899906842624) r0))) (let ((.def_183 (+ .def_182 .def_181 .def_180 .def_179))) (let ((.def_184 (<= .def_183 (/ 2605922565090263 4503599627370496)))) (let ((.def_185 (or b1 .def_184 .def_178))) (let ((.def_186 (* (/ 5651039200830413 4503599627370496) r3))) (let ((.def_187 (* (- (/ 7854145524665337 9007199254740992)) r2))) (let ((.def_188 (* (/ 1179826689189881 2251799813685248) r1))) (let ((.def_189 (* (- (/ 954992281683899 2251799813685248)) r0))) (let ((.def_190 (+ .def_189 .def_188 .def_187 .def_186))) (let ((.def_191 (<= .def_190 (/ 2218363317227153 4503599627370496)))) (let ((.def_192 (* (- (/ 3548311711395991 4503599627370496)) r3))) (let ((.def_193 (* (/ 521810357101667 281474976710656) r2))) (let ((.def_194 (* (- (/ 3920603833819605 9007199254740992)) r1))) (let ((.def_195 (* (- (/ 959282726779501 4503599627370496)) r0))) (let ((.def_196 (+ .def_195 .def_194 .def_193 .def_192))) (let ((.def_197 (<= .def_196 (/ 550142510656505 4503599627370496)))) (let ((.def_198 (or .def_158 .def_197 .def_191))) (let ((.def_199 (* (/ 296549199024311 562949953421312) r3))) (let ((.def_200 (* (- (/ 2594776753518103 4503599627370496)) r2))) (let ((.def_201 (* (/ 5447682015410293 9007199254740992) r1))) (let ((.def_202 (* (/ 1096893811069307 4503599627370496) r0))) (let ((.def_203 (+ .def_202 .def_201 .def_200 .def_199))) (let ((.def_204 (<= .def_203 (/ 1770097469533287 2251799813685248)))) (let ((.def_205 (* (/ 1986394021960367 1125899906842624) r3))) (let ((.def_206 (* (- (/ 3118062089179633 2251799813685248)) r2))) (let ((.def_207 (* (- (/ 4287495069181963 4503599627370496)) r1))) (let ((.def_208 (* (- (/ 344538308731053 4503599627370496)) r0))) (let ((.def_209 (+ .def_208 .def_207 .def_206 .def_205))) (let ((.def_210 (<= .def_209 (- (/ 828457222507055 2251799813685248))))) (let ((.def_211 (or .def_131 .def_210 .def_204))) (let ((.def_212 (* (/ 1910249462243177 4503599627370496) r3))) (let ((.def_213 (* (- (/ 2105578439499051 1125899906842624)) r2))) (let ((.def_214 (* (- (/ 7501811885067349 9007199254740992)) r1))) (let ((.def_215 (* (- (/ 165654495057713 4503599627370496)) r0))) (let ((.def_216 (+ .def_215 .def_214 .def_213 .def_212))) (let ((.def_217 (<= .def_216 (- (/ 448801065475445 2251799813685248))))) (let ((.def_218 (* (/ 2588790108933983 2251799813685248) r3))) (let ((.def_219 (* (- (/ 8570886717521529 9007199254740992)) r2))) (let ((.def_220 (* (- (/ 3815948794544329 1125899906842624)) r1))) (let ((.def_221 (* (/ 4484088387013749 2251799813685248) r0))) (let ((.def_222 (+ .def_221 .def_220 .def_219 .def_218))) (let ((.def_223 (<= .def_222 (- (/ 6502739368819095 9007199254740992))))) (let ((.def_224 (or b0 .def_223 .def_217))) (let ((.def_225 (* (/ 207512699859769 562949953421312) r3))) (let ((.def_226 (* (- (/ 8617903536279911 9007199254740992)) r2))) (let ((.def_227 (* (/ 1041683187199791 4503599627370496) r1))) (let ((.def_228 (* (/ 245391540077411 1125899906842624) r0))) (let ((.def_229 (+ .def_228 .def_227 .def_226 .def_225))) (let ((.def_230 (<= .def_229 (/ 1896489041421741 4503599627370496)))) (let ((.def_231 (* (- (/ 1527606822155335 4503599627370496)) r3))) (let ((.def_232 (* (- (/ 834140167627337 2251799813685248)) r2))) (let ((.def_233 (* (- (/ 1503443654172285 4503599627370496)) r1))) (let ((.def_234 (* (/ 137979451898027 140737488355328) r0))) (let ((.def_235 (+ .def_234 .def_233 .def_232 .def_231))) (let ((.def_236 (<= .def_235 (- (/ 327173668843045 4503599627370496))))) (let ((.def_237 (or .def_131 .def_236 .def_230))) (let ((.def_238 (* (/ 1545713495254887 2251799813685248) r3))) (let ((.def_239 (* (- (/ 1180056033995723 562949953421312)) r2))) (let ((.def_240 (* (/ 4736037177773109 4503599627370496) r1))) (let ((.def_241 (* (- (/ 934276392151171 1125899906842624)) r0))) (let ((.def_242 (+ .def_241 .def_240 .def_239 .def_238))) (let ((.def_243 (<= .def_242 (/ 2776377361125687 4503599627370496)))) (let ((.def_244 (* (/ 4810714468738769 2251799813685248) r3))) (let ((.def_245 (* (/ 5444291998076459 4503599627370496) r2))) (let ((.def_246 (* (/ 3530612524029343 4503599627370496) r1))) (let ((.def_247 (* (- (/ 2480599774621683 1125899906842624)) r0))) (let ((.def_248 (+ .def_247 .def_246 .def_245 .def_244))) (let ((.def_249 (<= .def_248 (/ 2330178232334077 2251799813685248)))) (let ((.def_250 (or b1 .def_249 .def_243))) (let ((.def_251 (* (- (/ 326278118023961 140737488355328)) r3))) (let ((.def_252 (* (/ 879640025162145 4503599627370496) r2))) (let ((.def_253 (* (/ 2820812354953009 4503599627370496) r1))) (let ((.def_254 (* (/ 2234442606449 17592186044416) r0))) (let ((.def_255 (+ .def_254 .def_253 .def_252 .def_251))) (let ((.def_256 (<= .def_255 (/ 156121564308079 562949953421312)))) (let ((.def_257 (* (- (/ 2126993448359881 2251799813685248)) r3))) (let ((.def_258 (* (/ 2945682881943889 9007199254740992) r2))) (let ((.def_259 (* (- (/ 383440215219769 281474976710656)) r1))) (let ((.def_260 (* (/ 1730577191987289 1125899906842624) r0))) (let ((.def_261 (+ .def_260 .def_259 .def_258 .def_257))) (let ((.def_262 (<= .def_261 (- (/ 320818950880695 1125899906842624))))) (let ((.def_263 (or b1 .def_262 .def_256))) (let ((.def_264 (* (- (/ 1430403530290049 4503599627370496)) r3))) (let ((.def_265 (* (/ 3104604668371157 2251799813685248) r2))) (let ((.def_266 (* (- (/ 1279178641153167 562949953421312)) r1))) (let ((.def_267 (* (/ 2377545906083625 4503599627370496) r0))) (let ((.def_268 (+ .def_267 .def_266 .def_265 .def_264))) (let ((.def_269 (<= .def_268 (/ 3812631854249929 4503599627370496)))) (let ((.def_270 (* (- (/ 2446708609334703 1125899906842624)) r3))) (let ((.def_271 (* (/ 654441642192027 562949953421312) r2))) (let ((.def_272 (* (/ 4457236675507151 9007199254740992) r1))) (let ((.def_273 (* (/ 2835771120790307 4503599627370496) r0))) (let ((.def_274 (+ .def_273 .def_272 .def_271 .def_270))) (let ((.def_275 (<= .def_274 (- (/ 24515568958161 281474976710656))))) (let ((.def_276 (or .def_158 .def_275 .def_269))) (let ((.def_277 (* (- (/ 4354303088403953 9007199254740992)) r3))) (let ((.def_278 (* (/ 977342971818963 2251799813685248) r2))) (let ((.def_279 (* (- (/ 393015307312577 281474976710656)) r1))) (let ((.def_280 (* (/ 2586940948347099 2251799813685248) r0))) (let ((.def_281 (+ .def_280 .def_279 .def_278 .def_277))) (let ((.def_282 (<= .def_281 (/ 2293333636252089 4503599627370496)))) (let ((.def_283 (* (/ 2640665322983159 2251799813685248) r3))) (let ((.def_284 (* (- (/ 3033429380545809 2251799813685248)) r2))) (let ((.def_285 (* (- (/ 7477630539940593 4503599627370496)) r1))) (let ((.def_286 (* (- (/ 619400427191989 1125899906842624)) r0))) (let ((.def_287 (+ .def_286 .def_285 .def_284 .def_283))) (let ((.def_288 (<= .def_287 (- (/ 2615207432085761 2251799813685248))))) (let ((.def_289 (or b2 .def_288 .def_282))) (let ((.def_290 (and .def_289 .def_276 .def_263 .def_250 .def_237 .def_224 .def_211 .def_198 .def_185 .def_172 .def_159 .def_145 .def_132 .def_118 .def_105 .def_92 .def_79 .def_66 .def_53 .def_40 .def_26 .def_13))) .def_290))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)