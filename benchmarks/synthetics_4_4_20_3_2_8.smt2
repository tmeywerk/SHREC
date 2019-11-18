(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(declare-fun b3 () Bool)
(assert (let ((.def_0 (* (/ 7634616237415749 9007199254740992) r3))) (let ((.def_1 (* (- (/ 1821669380701325 2251799813685248)) r2))) (let ((.def_2 (* (/ 8879037414743099 9007199254740992) r1))) (let ((.def_3 (* (/ 631505031189641 562949953421312) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 1288152225172927 1125899906842624)))) (let ((.def_6 (* (- (/ 650498564746701 9007199254740992)) r3))) (let ((.def_7 (* (/ 259333404888661 1125899906842624) r2))) (let ((.def_8 (* (- (/ 2485920474096213 9007199254740992)) r1))) (let ((.def_9 (* (- (/ 8116912046291883 9007199254740992)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 1203863771955793 2251799813685248))))) (let ((.def_12 (not b3))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (/ 4014245502105181 4503599627370496) r3))) (let ((.def_15 (* (/ 900320183733347 2251799813685248) r2))) (let ((.def_16 (* (/ 268166766237521 4503599627370496) r1))) (let ((.def_17 (* (- (/ 567560849564651 2251799813685248)) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (/ 3201242303955959 4503599627370496)))) (let ((.def_20 (* (- (/ 175098052126989 1125899906842624)) r3))) (let ((.def_21 (* (/ 1810216645503881 562949953421312) r2))) (let ((.def_22 (* (- (/ 7421438721787 4398046511104)) r1))) (let ((.def_23 (* (- (/ 6095668350366511 9007199254740992)) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 149347602141045 562949953421312)))) (let ((.def_26 (not b2))) (let ((.def_27 (or .def_26 .def_25 .def_19))) (let ((.def_28 (* (/ 9003090395104683 9007199254740992) r3))) (let ((.def_29 (* (- (/ 6671821860099173 9007199254740992)) r2))) (let ((.def_30 (* (- (/ 3371996374982637 4503599627370496)) r1))) (let ((.def_31 (* (- (/ 200086614444909 2251799813685248)) r0))) (let ((.def_32 (+ .def_31 .def_30 .def_29 .def_28))) (let ((.def_33 (<= .def_32 (/ 1001832750070615 4503599627370496)))) (let ((.def_34 (* (/ 471765442555801 281474976710656) r3))) (let ((.def_35 (* (/ 2194634504387913 9007199254740992) r2))) (let ((.def_36 (* (- (/ 3185839803579765 4503599627370496)) r1))) (let ((.def_37 (* (- (/ 1246662360067311 1125899906842624)) r0))) (let ((.def_38 (+ .def_37 .def_36 .def_35 .def_34))) (let ((.def_39 (<= .def_38 (/ 58324271194061 4503599627370496)))) (let ((.def_40 (or .def_12 .def_39 .def_33))) (let ((.def_41 (* (- (/ 3950787902295925 9007199254740992)) r3))) (let ((.def_42 (* (/ 1832855688204961 1125899906842624) r2))) (let ((.def_43 (* (- (/ 836106454871537 562949953421312)) r1))) (let ((.def_44 (* (/ 4603456839324835 2251799813685248) r0))) (let ((.def_45 (+ .def_44 .def_43 .def_42 .def_41))) (let ((.def_46 (<= .def_45 (/ 8062071302308941 9007199254740992)))) (let ((.def_47 (* (/ 77296878750411 281474976710656) r3))) (let ((.def_48 (* (- (/ 4658135325921391 9007199254740992)) r2))) (let ((.def_49 (* (/ 2883369804809013 1125899906842624) r1))) (let ((.def_50 (* (- (/ 4255347439153403 2251799813685248)) r0))) (let ((.def_51 (+ .def_50 .def_49 .def_48 .def_47))) (let ((.def_52 (<= .def_51 (/ 793642076989369 4503599627370496)))) (let ((.def_53 (or b0 .def_52 .def_46))) (let ((.def_54 (* (/ 5734008805072249 2251799813685248) r3))) (let ((.def_55 (* (- (/ 856134781572857 1125899906842624)) r2))) (let ((.def_56 (* (- (/ 4925823454725707 4503599627370496)) r1))) (let ((.def_57 (* (- (/ 1300218597479819 2251799813685248)) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (/ 5548536921997449 9007199254740992)))) (let ((.def_60 (* (/ 1947208712420823 9007199254740992) r3))) (let ((.def_61 (* (/ 5007610433004827 4503599627370496) r2))) (let ((.def_62 (* (- (/ 874376086611393 9007199254740992)) r1))) (let ((.def_63 (* (- (/ 333357619213857 2251799813685248)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 1291547878591377 2251799813685248)))) (let ((.def_66 (or .def_26 .def_65 .def_59))) (let ((.def_67 (* (- (/ 5330316750920925 9007199254740992)) r3))) (let ((.def_68 (* (/ 21774133657995 70368744177664) r2))) (let ((.def_69 (* (- (/ 4082597954790479 4503599627370496)) r1))) (let ((.def_70 (* (- (/ 1758524505835993 4503599627370496)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 2659670204332201 4503599627370496))))) (let ((.def_73 (* (/ 8011908508401413 4503599627370496) r3))) (let ((.def_74 (* (- (/ 2458421351290457 2251799813685248)) r2))) (let ((.def_75 (* (/ 621200074321351 2251799813685248) r1))) (let ((.def_76 (* (- (/ 2628901546136937 4503599627370496)) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (/ 38963866274155 562949953421312)))) (let ((.def_79 (or .def_26 .def_78 .def_72))) (let ((.def_80 (* (- (/ 8321864106906985 9007199254740992)) r3))) (let ((.def_81 (* (/ 2939291726180707 4503599627370496) r2))) (let ((.def_82 (* (- (/ 2341878340974753 1125899906842624)) r1))) (let ((.def_83 (* (- (/ 13258564624109 70368744177664)) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (- (/ 568589292274491 2251799813685248))))) (let ((.def_86 (* (- (/ 1820368705107367 4503599627370496)) r3))) (let ((.def_87 (* (/ 3091534930297351 4503599627370496) r2))) (let ((.def_88 (* (/ 153891883084041 1125899906842624) r1))) (let ((.def_89 (* (/ 1070108406592933 4503599627370496) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (/ 1651170034082727 4503599627370496)))) (let ((.def_92 (or .def_26 .def_91 .def_85))) (let ((.def_93 (* (/ 2014016424089263 4503599627370496) r3))) (let ((.def_94 (* (- (/ 8451106425298063 9007199254740992)) r2))) (let ((.def_95 (* (- (/ 2774545137265199 9007199254740992)) r1))) (let ((.def_96 (* (/ 1202369499479249 2251799813685248) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (/ 159559705498709 562949953421312)))) (let ((.def_99 (* (/ 853919822283227 281474976710656) r3))) (let ((.def_100 (* (- (/ 6876364249402515 4503599627370496)) r2))) (let ((.def_101 (* (/ 3997183436727431 2251799813685248) r1))) (let ((.def_102 (* (- (/ 2770201104600751 4503599627370496)) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (/ 2531045290392595 2251799813685248)))) (let ((.def_105 (or .def_26 .def_104 .def_98))) (let ((.def_106 (* (/ 2496609899849617 9007199254740992) r3))) (let ((.def_107 (* (- (/ 3679486082092039 4503599627370496)) r2))) (let ((.def_108 (* (- (/ 913098477879627 2251799813685248)) r1))) (let ((.def_109 (* (/ 2330381028700625 2251799813685248) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (/ 2676596787523049 4503599627370496)))) (let ((.def_112 (* (/ 3637736353616995 2251799813685248) r3))) (let ((.def_113 (* (/ 2711225565483161 4503599627370496) r2))) (let ((.def_114 (* (- (/ 29128759509853 140737488355328)) r1))) (let ((.def_115 (* (/ 2629779595596853 2251799813685248) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (/ 7170417842557349 4503599627370496)))) (let ((.def_118 (or b0 .def_117 .def_111))) (let ((.def_119 (* (- (/ 3612183360017609 9007199254740992)) r3))) (let ((.def_120 (* (- (/ 3272121928636913 9007199254740992)) r2))) (let ((.def_121 (* (/ 150955262113305 9007199254740992) r1))) (let ((.def_122 (* (/ 4657224109234929 9007199254740992) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (/ 778178201084369 4503599627370496)))) (let ((.def_125 (* (/ 6069711250833431 4503599627370496) r3))) (let ((.def_126 (* (- (/ 655223704824259 4503599627370496)) r2))) (let ((.def_127 (* (- (/ 1950830570701983 4503599627370496)) r1))) (let ((.def_128 (* (/ 3286659861544613 2251799813685248) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (/ 2605722214134763 2251799813685248)))) (let ((.def_131 (or .def_12 .def_130 .def_124))) (let ((.def_132 (* (- (/ 90319671437051 70368744177664)) r3))) (let ((.def_133 (* (/ 3876314696432745 9007199254740992) r2))) (let ((.def_134 (* (/ 2810955198155443 4503599627370496) r1))) (let ((.def_135 (* (/ 5861023958661525 9007199254740992) r0))) (let ((.def_136 (+ .def_135 .def_134 .def_133 .def_132))) (let ((.def_137 (<= .def_136 (/ 1259551833616945 4503599627370496)))) (let ((.def_138 (* (/ 3020765489014555 1125899906842624) r3))) (let ((.def_139 (* (/ 309921849498227 4503599627370496) r2))) (let ((.def_140 (* (- (/ 1273069761265725 9007199254740992)) r1))) (let ((.def_141 (* (- (/ 403845904134989 281474976710656)) r0))) (let ((.def_142 (+ .def_141 .def_140 .def_139 .def_138))) (let ((.def_143 (<= .def_142 (/ 538726923602955 1125899906842624)))) (let ((.def_144 (or b1 .def_143 .def_137))) (let ((.def_145 (* (- (/ 4144328493810207 4503599627370496)) r3))) (let ((.def_146 (* (/ 1708596879526017 4503599627370496) r2))) (let ((.def_147 (* (- (/ 2437909379324345 9007199254740992)) r1))) (let ((.def_148 (* (- (/ 5529664482916139 4503599627370496)) r0))) (let ((.def_149 (+ .def_148 .def_147 .def_146 .def_145))) (let ((.def_150 (<= .def_149 (- (/ 1604126426250705 4503599627370496))))) (let ((.def_151 (* (- (/ 2241995384541355 4503599627370496)) r3))) (let ((.def_152 (* (- (/ 1139615813617135 2251799813685248)) r2))) (let ((.def_153 (* (- (/ 4526712285434229 1125899906842624)) r1))) (let ((.def_154 (* (/ 6753002970805255 9007199254740992) r0))) (let ((.def_155 (+ .def_154 .def_153 .def_152 .def_151))) (let ((.def_156 (<= .def_155 (- (/ 1349262801810111 562949953421312))))) (let ((.def_157 (or b3 .def_156 .def_150))) (let ((.def_158 (* (/ 3150826661883969 2251799813685248) r3))) (let ((.def_159 (* (- (/ 148197818275625 140737488355328)) r2))) (let ((.def_160 (* (- (/ 2231639630721909 9007199254740992)) r1))) (let ((.def_161 (* (- (/ 4358228972807633 2251799813685248)) r0))) (let ((.def_162 (+ .def_161 .def_160 .def_159 .def_158))) (let ((.def_163 (<= .def_162 (/ 2841102198568151 9007199254740992)))) (let ((.def_164 (* (/ 1184076270620913 1125899906842624) r3))) (let ((.def_165 (* (- (/ 1298242895375647 4503599627370496)) r2))) (let ((.def_166 (* (- (/ 1402063225470161 2251799813685248)) r1))) (let ((.def_167 (* (- (/ 512847179957591 562949953421312)) r0))) (let ((.def_168 (+ .def_167 .def_166 .def_165 .def_164))) (let ((.def_169 (<= .def_168 (- (/ 3446380091019805 9007199254740992))))) (let ((.def_170 (or b1 .def_169 .def_163))) (let ((.def_171 (* (/ 3458489794750559 4503599627370496) r3))) (let ((.def_172 (* (/ 1669083075718931 4503599627370496) r2))) (let ((.def_173 (* (- (/ 1523856227969385 4503599627370496)) r1))) (let ((.def_174 (* (- (/ 4250372215908333 4503599627370496)) r0))) (let ((.def_175 (+ .def_174 .def_173 .def_172 .def_171))) (let ((.def_176 (<= .def_175 (/ 1181457378488561 2251799813685248)))) (let ((.def_177 (* (- (/ 1362890712517893 9007199254740992)) r3))) (let ((.def_178 (* (/ 620357268463095 4503599627370496) r2))) (let ((.def_179 (* (- (/ 891670486389645 4503599627370496)) r1))) (let ((.def_180 (* (- (/ 399449180149611 1125899906842624)) r0))) (let ((.def_181 (+ .def_180 .def_179 .def_178 .def_177))) (let ((.def_182 (<= .def_181 (- (/ 1314094285538981 4503599627370496))))) (let ((.def_183 (or b2 .def_182 .def_176))) (let ((.def_184 (* (- (/ 6130308031121673 9007199254740992)) r3))) (let ((.def_185 (* (- (/ 2446156996062119 2251799813685248)) r2))) (let ((.def_186 (* (- (/ 7874936409934371 9007199254740992)) r1))) (let ((.def_187 (* (- (/ 527844476571483 2251799813685248)) r0))) (let ((.def_188 (+ .def_187 .def_186 .def_185 .def_184))) (let ((.def_189 (<= .def_188 (- (/ 3387375391178299 4503599627370496))))) (let ((.def_190 (* (- (/ 1358345327897719 4503599627370496)) r3))) (let ((.def_191 (* (- (/ 3038232380625849 4503599627370496)) r2))) (let ((.def_192 (* (- (/ 2427892094168739 2251799813685248)) r1))) (let ((.def_193 (* (/ 1931157138597965 2251799813685248) r0))) (let ((.def_194 (+ .def_193 .def_192 .def_191 .def_190))) (let ((.def_195 (<= .def_194 (- (/ 749640847862135 1125899906842624))))) (let ((.def_196 (or b2 .def_195 .def_189))) (let ((.def_197 (* (/ 1233963732265253 2251799813685248) r3))) (let ((.def_198 (* (/ 970370104689729 2251799813685248) r2))) (let ((.def_199 (* (- (/ 1046631716616543 4503599627370496)) r1))) (let ((.def_200 (* (/ 2511701334346065 2251799813685248) r0))) (let ((.def_201 (+ .def_200 .def_199 .def_198 .def_197))) (let ((.def_202 (<= .def_201 (/ 183674193114425 140737488355328)))) (let ((.def_203 (* (/ 8420183959582383 9007199254740992) r3))) (let ((.def_204 (* (- (/ 1406923246707439 1125899906842624)) r2))) (let ((.def_205 (* (/ 8169815058914243 9007199254740992) r1))) (let ((.def_206 (* (- (/ 4023249947939905 4503599627370496)) r0))) (let ((.def_207 (+ .def_206 .def_205 .def_204 .def_203))) (let ((.def_208 (<= .def_207 (- (/ 1063041629953335 4503599627370496))))) (let ((.def_209 (or .def_26 .def_208 .def_202))) (let ((.def_210 (* (- (/ 2778902813570851 2251799813685248)) r3))) (let ((.def_211 (* (- (/ 8151593452065165 4503599627370496)) r2))) (let ((.def_212 (* (/ 1254090463687861 4503599627370496) r1))) (let ((.def_213 (* (- (/ 244799412662715 2251799813685248)) r0))) (let ((.def_214 (+ .def_213 .def_212 .def_211 .def_210))) (let ((.def_215 (<= .def_214 (- (/ 1970039755066209 4503599627370496))))) (let ((.def_216 (* (- (/ 2273684191676039 2251799813685248)) r3))) (let ((.def_217 (* (- (/ 1354548397360177 1125899906842624)) r2))) (let ((.def_218 (* (- (/ 3021249627045437 2251799813685248)) r1))) (let ((.def_219 (* (- (/ 269203575123959 562949953421312)) r0))) (let ((.def_220 (+ .def_219 .def_218 .def_217 .def_216))) (let ((.def_221 (<= .def_220 (- (/ 2352597269218255 1125899906842624))))) (let ((.def_222 (or .def_26 .def_221 .def_215))) (let ((.def_223 (* (- (/ 3949113677321301 2251799813685248)) r3))) (let ((.def_224 (* (- (/ 6577508164210447 9007199254740992)) r2))) (let ((.def_225 (* (/ 701377415087319 2251799813685248) r1))) (let ((.def_226 (* (- (/ 1761862881281955 2251799813685248)) r0))) (let ((.def_227 (+ .def_226 .def_225 .def_224 .def_223))) (let ((.def_228 (<= .def_227 (- (/ 8203977954605597 9007199254740992))))) (let ((.def_229 (* (- (/ 259678061042869 1125899906842624)) r3))) (let ((.def_230 (* (- (/ 473894629631955 4503599627370496)) r2))) (let ((.def_231 (* (- (/ 7481208996763097 4503599627370496)) r1))) (let ((.def_232 (* (/ 2668862400748223 4503599627370496) r0))) (let ((.def_233 (+ .def_232 .def_231 .def_230 .def_229))) (let ((.def_234 (<= .def_233 (- (/ 400111583594495 562949953421312))))) (let ((.def_235 (not b1))) (let ((.def_236 (or .def_235 .def_234 .def_228))) (let ((.def_237 (* (- (/ 921327223177963 2251799813685248)) r3))) (let ((.def_238 (* (- (/ 799520365694711 9007199254740992)) r2))) (let ((.def_239 (* (- (/ 70702392506725 9007199254740992)) r1))) (let ((.def_240 (* (/ 1775909653747599 1125899906842624) r0))) (let ((.def_241 (+ .def_240 .def_239 .def_238 .def_237))) (let ((.def_242 (<= .def_241 (/ 191902574942989 281474976710656)))) (let ((.def_243 (* (- (/ 69456279097021 2251799813685248)) r3))) (let ((.def_244 (* (/ 140388506163261 9007199254740992) r2))) (let ((.def_245 (* (/ 933352954271307 1125899906842624) r1))) (let ((.def_246 (* (- (/ 3460610490266891 2251799813685248)) r0))) (let ((.def_247 (+ .def_246 .def_245 .def_244 .def_243))) (let ((.def_248 (<= .def_247 (- (/ 1684071993727621 4503599627370496))))) (let ((.def_249 (or b2 .def_248 .def_242))) (let ((.def_250 (* (- (/ 824273241495057 4503599627370496)) r3))) (let ((.def_251 (* (/ 277980890009125 4503599627370496) r2))) (let ((.def_252 (* (- (/ 279524858649037 4503599627370496)) r1))) (let ((.def_253 (* (/ 239038428858949 562949953421312) r0))) (let ((.def_254 (+ .def_253 .def_252 .def_251 .def_250))) (let ((.def_255 (<= .def_254 (/ 3185455242665463 9007199254740992)))) (let ((.def_256 (* (- (/ 8309026242383437 4503599627370496)) r3))) (let ((.def_257 (* (- (/ 85203056303073 4503599627370496)) r2))) (let ((.def_258 (* (/ 249572762363595 562949953421312) r1))) (let ((.def_259 (* (- (/ 4705161484142931 9007199254740992)) r0))) (let ((.def_260 (+ .def_259 .def_258 .def_257 .def_256))) (let ((.def_261 (<= .def_260 (- (/ 4391003964743579 4503599627370496))))) (let ((.def_262 (or .def_12 .def_261 .def_255))) (let ((.def_263 (and .def_262 .def_249 .def_236 .def_222 .def_209 .def_196 .def_183 .def_170 .def_157 .def_144 .def_131 .def_118 .def_105 .def_92 .def_79 .def_66 .def_53 .def_40 .def_27 .def_13))) .def_263)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
