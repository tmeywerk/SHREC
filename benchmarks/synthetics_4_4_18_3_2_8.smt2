(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun b1 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 661343236516193 1125899906842624) r3))) (let ((.def_1 (* (- (/ 3327865805607473 4503599627370496)) r2))) (let ((.def_2 (* (- (/ 1699856297553003 2251799813685248)) r1))) (let ((.def_3 (* (/ 190106446774889 140737488355328) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 626352507459885 1125899906842624)))) (let ((.def_6 (* (/ 6264666949186125 4503599627370496) r3))) (let ((.def_7 (* (/ 1857010121210641 1125899906842624) r2))) (let ((.def_8 (* (/ 646442862665783 4503599627370496) r1))) (let ((.def_9 (* (- (/ 7847990253972923 9007199254740992)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 4972622752142541 4503599627370496)))) (let ((.def_12 (or b1 .def_11 .def_5))) (let ((.def_13 (* (/ 2773851313233613 4503599627370496) r3))) (let ((.def_14 (* (- (/ 4532324568472243 9007199254740992)) r2))) (let ((.def_15 (* (- (/ 25035536309195 17592186044416)) r1))) (let ((.def_16 (* (/ 1182363958392555 2251799813685248) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (/ 2481173494632681 9007199254740992)))) (let ((.def_19 (* (/ 7964603499283671 4503599627370496) r3))) (let ((.def_20 (* (/ 301305399100869 9007199254740992) r2))) (let ((.def_21 (* (/ 26651981931045 281474976710656) r1))) (let ((.def_22 (* (/ 567227586616813 562949953421312) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (/ 6586433361226527 4503599627370496)))) (let ((.def_25 (not b2))) (let ((.def_26 (or .def_25 .def_24 .def_18))) (let ((.def_27 (* (- (/ 1196546971560587 4503599627370496)) r3))) (let ((.def_28 (* (/ 681409661544621 1125899906842624) r2))) (let ((.def_29 (* (/ 74283322614103 2251799813685248) r1))) (let ((.def_30 (* (/ 1513147225938595 2251799813685248) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 444862493292131 562949953421312)))) (let ((.def_33 (* (- (/ 4239102633900693 9007199254740992)) r3))) (let ((.def_34 (* (/ 3696704046433553 9007199254740992) r2))) (let ((.def_35 (* (/ 2466279906854831 2251799813685248) r1))) (let ((.def_36 (* (- (/ 1685028798883397 1125899906842624)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 3120707407448699 9007199254740992))))) (let ((.def_39 (or .def_25 .def_38 .def_32))) (let ((.def_40 (* (- (/ 3417678513040831 4503599627370496)) r3))) (let ((.def_41 (* (/ 1031574061287447 1125899906842624) r2))) (let ((.def_42 (* (- (/ 129049339459185 4503599627370496)) r1))) (let ((.def_43 (* (/ 26053337811519 2251799813685248) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (/ 856134327143793 9007199254740992)))) (let ((.def_46 (* (/ 2424596786730997 1125899906842624) r3))) (let ((.def_47 (* (- (/ 7150259769430257 2251799813685248)) r2))) (let ((.def_48 (* (/ 52712627146133 1125899906842624) r1))) (let ((.def_49 (* (- (/ 1449108976276193 9007199254740992)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 2089766372806279 2251799813685248))))) (let ((.def_52 (or .def_25 .def_51 .def_45))) (let ((.def_53 (* (- (/ 3750683733104401 9007199254740992)) r3))) (let ((.def_54 (* (- (/ 5339432816772477 9007199254740992)) r2))) (let ((.def_55 (* (- (/ 4115605773990017 9007199254740992)) r1))) (let ((.def_56 (* (- (/ 2257699470806517 4503599627370496)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (- (/ 1731411704951115 2251799813685248))))) (let ((.def_59 (* (- (/ 853005680968161 4503599627370496)) r3))) (let ((.def_60 (* (/ 1246747162907871 562949953421312) r2))) (let ((.def_61 (* (- (/ 3579647485451099 2251799813685248)) r1))) (let ((.def_62 (* (/ 251348631740127 1125899906842624) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (/ 3130055791542559 9007199254740992)))) (let ((.def_65 (not b3))) (let ((.def_66 (or .def_65 .def_64 .def_58))) (let ((.def_67 (* (/ 3668367645503907 9007199254740992) r3))) (let ((.def_68 (* (- (/ 5348316724418323 4503599627370496)) r2))) (let ((.def_69 (* (- (/ 918397076622569 2251799813685248)) r1))) (let ((.def_70 (* (- (/ 136942102111151 70368744177664)) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (- (/ 6368010731269871 9007199254740992))))) (let ((.def_73 (* (/ 1969589368402551 9007199254740992) r3))) (let ((.def_74 (* (/ 179750212361197 1125899906842624) r2))) (let ((.def_75 (* (/ 598471870353379 1125899906842624) r1))) (let ((.def_76 (* (- (/ 1013382962037903 562949953421312)) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 1298669900976649 2251799813685248))))) (let ((.def_79 (or b3 .def_78 .def_72))) (let ((.def_80 (* (- (/ 129450920998727 9007199254740992)) r3))) (let ((.def_81 (* (- (/ 3653021823530175 2251799813685248)) r2))) (let ((.def_82 (* (/ 1146086790014843 2251799813685248) r1))) (let ((.def_83 (* (/ 1432075165137259 9007199254740992) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (/ 478894245164393 4503599627370496)))) (let ((.def_86 (* (/ 2283662503993147 4503599627370496) r3))) (let ((.def_87 (* (- (/ 1965140092677979 2251799813685248)) r2))) (let ((.def_88 (* (- (/ 1216883609601975 1125899906842624)) r1))) (let ((.def_89 (* (/ 1779447313255767 1125899906842624) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (/ 1246459143324935 9007199254740992)))) (let ((.def_92 (or .def_65 .def_91 .def_85))) (let ((.def_93 (* (- (/ 47387497816345 562949953421312)) r3))) (let ((.def_94 (* (/ 58342849968785 70368744177664) r2))) (let ((.def_95 (* (- (/ 1493679732569021 4503599627370496)) r1))) (let ((.def_96 (* (/ 357656400293403 2251799813685248) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (/ 4697818941109471 9007199254740992)))) (let ((.def_99 (* (/ 2760933961751009 4503599627370496) r3))) (let ((.def_100 (* (- (/ 1726563546533583 4503599627370496)) r2))) (let ((.def_101 (* (- (/ 2667934045946023 4503599627370496)) r1))) (let ((.def_102 (* (- (/ 4759055610470845 4503599627370496)) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (- (/ 7029262154630035 9007199254740992))))) (let ((.def_105 (or b1 .def_104 .def_98))) (let ((.def_106 (* (- (/ 5451270982237613 9007199254740992)) r3))) (let ((.def_107 (* (- (/ 1993916697323739 1125899906842624)) r2))) (let ((.def_108 (* (- (/ 82313450164375 70368744177664)) r1))) (let ((.def_109 (* (/ 185374901767049 4503599627370496) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (- (/ 589480020498395 562949953421312))))) (let ((.def_112 (* (/ 243868806489459 4503599627370496) r3))) (let ((.def_113 (* (/ 155992581380767 9007199254740992) r2))) (let ((.def_114 (* (- (/ 254111275996837 2251799813685248)) r1))) (let ((.def_115 (* (- (/ 1052963165553049 1125899906842624)) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (- (/ 4809350878823775 9007199254740992))))) (let ((.def_118 (or b3 .def_117 .def_111))) (let ((.def_119 (* (- (/ 663333303160907 2251799813685248)) r3))) (let ((.def_120 (* (- (/ 4218097375782805 9007199254740992)) r2))) (let ((.def_121 (* (/ 302304122278381 4503599627370496) r1))) (let ((.def_122 (* (/ 2295733480517053 1125899906842624) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (/ 1785572764373019 1125899906842624)))) (let ((.def_125 (* (- (/ 1846509596850327 9007199254740992)) r3))) (let ((.def_126 (* (- (/ 552762746621711 4503599627370496)) r2))) (let ((.def_127 (* (/ 540593164914443 1125899906842624) r1))) (let ((.def_128 (* (/ 507656917429191 4503599627370496) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (/ 1253204595223247 9007199254740992)))) (let ((.def_131 (or b3 .def_130 .def_124))) (let ((.def_132 (* (- (/ 4182269073067543 4503599627370496)) r3))) (let ((.def_133 (* (/ 1688197314828083 1125899906842624) r2))) (let ((.def_134 (* (- (/ 183918162429525 562949953421312)) r1))) (let ((.def_135 (* (- (/ 10577443131697 140737488355328)) r0))) (let ((.def_136 (+ .def_135 .def_134 .def_133 .def_132))) (let ((.def_137 (<= .def_136 (/ 2996386007706081 4503599627370496)))) (let ((.def_138 (* (/ 7459159145847329 9007199254740992) r3))) (let ((.def_139 (* (/ 3576055885087769 4503599627370496) r2))) (let ((.def_140 (* (/ 917042658541105 562949953421312) r1))) (let ((.def_141 (* (- (/ 100347165164523 9007199254740992)) r0))) (let ((.def_142 (+ .def_141 .def_140 .def_139 .def_138))) (let ((.def_143 (<= .def_142 (/ 3453493987434087 2251799813685248)))) (let ((.def_144 (or b3 .def_143 .def_137))) (let ((.def_145 (* (/ 36055165938129 9007199254740992) r3))) (let ((.def_146 (* (/ 2545663397189811 2251799813685248) r2))) (let ((.def_147 (* (- (/ 649046564870553 2251799813685248)) r1))) (let ((.def_148 (* (- (/ 2756480170338113 2251799813685248)) r0))) (let ((.def_149 (+ .def_148 .def_147 .def_146 .def_145))) (let ((.def_150 (<= .def_149 (/ 533286600463217 2251799813685248)))) (let ((.def_151 (* (/ 8207236561335657 9007199254740992) r3))) (let ((.def_152 (* (- (/ 1756136351714745 9007199254740992)) r2))) (let ((.def_153 (* (- (/ 6046663444549479 9007199254740992)) r1))) (let ((.def_154 (* (/ 593551474461635 562949953421312) r0))) (let ((.def_155 (+ .def_154 .def_153 .def_152 .def_151))) (let ((.def_156 (<= .def_155 (/ 4450546922986805 9007199254740992)))) (let ((.def_157 (or b2 .def_156 .def_150))) (let ((.def_158 (* (/ 1017578761873 2251799813685248) r3))) (let ((.def_159 (* (- (/ 2364527659355311 2251799813685248)) r2))) (let ((.def_160 (* (- (/ 1197017002615187 4503599627370496)) r1))) (let ((.def_161 (* (/ 2405886738190371 9007199254740992) r0))) (let ((.def_162 (+ .def_161 .def_160 .def_159 .def_158))) (let ((.def_163 (<= .def_162 (- (/ 2391900625353723 9007199254740992))))) (let ((.def_164 (* (/ 4917096426905147 4503599627370496) r3))) (let ((.def_165 (* (/ 8571035029469225 9007199254740992) r2))) (let ((.def_166 (* (- (/ 3016782382362515 9007199254740992)) r1))) (let ((.def_167 (* (- (/ 2641536856160831 2251799813685248)) r0))) (let ((.def_168 (+ .def_167 .def_166 .def_165 .def_164))) (let ((.def_169 (<= .def_168 (/ 61067419170021 281474976710656)))) (let ((.def_170 (or b0 .def_169 .def_163))) (let ((.def_171 (* (/ 1214580189244849 4503599627370496) r3))) (let ((.def_172 (* (- (/ 4382597878517883 9007199254740992)) r2))) (let ((.def_173 (* (/ 4612507884262685 4503599627370496) r1))) (let ((.def_174 (* (/ 71673015475451 2251799813685248) r0))) (let ((.def_175 (+ .def_174 .def_173 .def_172 .def_171))) (let ((.def_176 (<= .def_175 (/ 8241693143711275 9007199254740992)))) (let ((.def_177 (* (/ 2067718000600453 2251799813685248) r3))) (let ((.def_178 (* (/ 52571289127235 281474976710656) r2))) (let ((.def_179 (* (/ 5604687587081287 1125899906842624) r1))) (let ((.def_180 (* (/ 3284811485026627 9007199254740992) r0))) (let ((.def_181 (+ .def_180 .def_179 .def_178 .def_177))) (let ((.def_182 (<= .def_181 (/ 1698563454880601 562949953421312)))) (let ((.def_183 (or .def_65 .def_182 .def_176))) (let ((.def_184 (* (/ 977701427231445 2251799813685248) r3))) (let ((.def_185 (* (/ 789759184543763 2251799813685248) r2))) (let ((.def_186 (* (- (/ 3361232434627621 9007199254740992)) r1))) (let ((.def_187 (* (/ 344482093514063 4503599627370496) r0))) (let ((.def_188 (+ .def_187 .def_186 .def_185 .def_184))) (let ((.def_189 (<= .def_188 (/ 740601762193539 2251799813685248)))) (let ((.def_190 (* (- (/ 5341133435413151 2251799813685248)) r3))) (let ((.def_191 (* (/ 202253561505933 1125899906842624) r2))) (let ((.def_192 (* (/ 67288251441029 562949953421312) r1))) (let ((.def_193 (* (/ 244177171500575 562949953421312) r0))) (let ((.def_194 (+ .def_193 .def_192 .def_191 .def_190))) (let ((.def_195 (<= .def_194 (- (/ 7444385095562795 9007199254740992))))) (let ((.def_196 (or b3 .def_195 .def_189))) (let ((.def_197 (* (- (/ 2073722882880709 2251799813685248)) r3))) (let ((.def_198 (* (/ 4479486426290363 4503599627370496) r2))) (let ((.def_199 (* (- (/ 1218938547235801 1125899906842624)) r1))) (let ((.def_200 (* (- (/ 8918230047809929 4503599627370496)) r0))) (let ((.def_201 (+ .def_200 .def_199 .def_198 .def_197))) (let ((.def_202 (<= .def_201 (- (/ 1427958795686575 4503599627370496))))) (let ((.def_203 (* (- (/ 1899072423383525 9007199254740992)) r3))) (let ((.def_204 (* (/ 3415897334225579 9007199254740992) r2))) (let ((.def_205 (* (- (/ 1984044834390485 9007199254740992)) r1))) (let ((.def_206 (* (- (/ 8208760936823891 9007199254740992)) r0))) (let ((.def_207 (+ .def_206 .def_205 .def_204 .def_203))) (let ((.def_208 (<= .def_207 (- (/ 284930421592049 562949953421312))))) (let ((.def_209 (not b1))) (let ((.def_210 (or .def_209 .def_208 .def_202))) (let ((.def_211 (* (- (/ 3395886781205271 9007199254740992)) r3))) (let ((.def_212 (* (- (/ 310612307587711 562949953421312)) r2))) (let ((.def_213 (* (/ 6493419639203407 9007199254740992) r1))) (let ((.def_214 (* (- (/ 1201907796740073 4503599627370496)) r0))) (let ((.def_215 (+ .def_214 .def_213 .def_212 .def_211))) (let ((.def_216 (<= .def_215 (/ 511828746514481 4503599627370496)))) (let ((.def_217 (* (/ 391632698666507 281474976710656) r3))) (let ((.def_218 (* (- (/ 6988331609029473 9007199254740992)) r2))) (let ((.def_219 (* (- (/ 2492800349581043 9007199254740992)) r1))) (let ((.def_220 (* (- (/ 387284753411773 1125899906842624)) r0))) (let ((.def_221 (+ .def_220 .def_219 .def_218 .def_217))) (let ((.def_222 (<= .def_221 (- (/ 838878303483735 9007199254740992))))) (let ((.def_223 (or b1 .def_222 .def_216))) (let ((.def_224 (* (- (/ 229554954054771 9007199254740992)) r3))) (let ((.def_225 (* (- (/ 5741894555488665 2251799813685248)) r2))) (let ((.def_226 (* (- (/ 1241767547359785 562949953421312)) r1))) (let ((.def_227 (* (- (/ 8833464517140503 9007199254740992)) r0))) (let ((.def_228 (+ .def_227 .def_226 .def_225 .def_224))) (let ((.def_229 (<= .def_228 (- (/ 3837443761418337 2251799813685248))))) (let ((.def_230 (* (- (/ 643078441542523 9007199254740992)) r3))) (let ((.def_231 (* (- (/ 3972130387674389 9007199254740992)) r2))) (let ((.def_232 (* (/ 717095239751459 562949953421312) r1))) (let ((.def_233 (* (- (/ 1391893582551327 2251799813685248)) r0))) (let ((.def_234 (+ .def_233 .def_232 .def_231 .def_230))) (let ((.def_235 (<= .def_234 (/ 76301797047773 2251799813685248)))) (let ((.def_236 (or .def_25 .def_235 .def_229))) (let ((.def_237 (and .def_236 .def_223 .def_210 .def_196 .def_183 .def_170 .def_157 .def_144 .def_131 .def_118 .def_105 .def_92 .def_79 .def_66 .def_52 .def_39 .def_26 .def_12))) .def_237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
