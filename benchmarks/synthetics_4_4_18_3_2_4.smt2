(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun b1 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (- (/ 2643589981872393 4503599627370496)) r3))) (let ((.def_1 (* (- (/ 1232326567699873 2251799813685248)) r2))) (let ((.def_2 (* (- (/ 5823038148263863 9007199254740992)) r1))) (let ((.def_3 (* (/ 756331301147531 2251799813685248) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 195465500754119 281474976710656))))) (let ((.def_6 (* (/ 2125773178247009 1125899906842624) r3))) (let ((.def_7 (* (- (/ 1521915880691641 4503599627370496)) r2))) (let ((.def_8 (* (/ 8856275561381905 9007199254740992) r1))) (let ((.def_9 (* (- (/ 5683149332248061 4503599627370496)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 5327539872731381 9007199254740992)))) (let ((.def_12 (not b1))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (/ 1017288151515849 2251799813685248) r3))) (let ((.def_15 (* (- (/ 1489184786874241 2251799813685248)) r2))) (let ((.def_16 (* (- (/ 508855954054641 1125899906842624)) r1))) (let ((.def_17 (* (/ 1577857158859579 9007199254740992) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 2319289121895383 9007199254740992))))) (let ((.def_20 (* (- (/ 903819291605209 1125899906842624)) r3))) (let ((.def_21 (* (/ 5668108392537877 2251799813685248) r2))) (let ((.def_22 (* (/ 7349889009044015 9007199254740992) r1))) (let ((.def_23 (* (- (/ 2805420153552081 1125899906842624)) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 349192042831201 9007199254740992)))) (let ((.def_26 (or b0 .def_25 .def_19))) (let ((.def_27 (* (- (/ 7723391736581731 9007199254740992)) r3))) (let ((.def_28 (* (/ 1579953109905091 2251799813685248) r2))) (let ((.def_29 (* (- (/ 2339836055071847 1125899906842624)) r1))) (let ((.def_30 (* (- (/ 538868911785215 2251799813685248)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (- (/ 2314940953060211 4503599627370496))))) (let ((.def_33 (* (/ 1111827374436819 2251799813685248) r3))) (let ((.def_34 (* (- (/ 1644397877119651 9007199254740992)) r2))) (let ((.def_35 (* (- (/ 570892148646975 4503599627370496)) r1))) (let ((.def_36 (* (- (/ 400635739566177 562949953421312)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 1439406275356803 4503599627370496))))) (let ((.def_39 (or b2 .def_38 .def_32))) (let ((.def_40 (* (/ 2758076365361485 4503599627370496) r3))) (let ((.def_41 (* (/ 1115987023337691 2251799813685248) r2))) (let ((.def_42 (* (/ 103344352788199 281474976710656) r1))) (let ((.def_43 (* (- (/ 675417045839659 2251799813685248)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (/ 1049523500162655 1125899906842624)))) (let ((.def_46 (* (/ 1806118317580065 1125899906842624) r3))) (let ((.def_47 (* (/ 1187464624384153 2251799813685248) r2))) (let ((.def_48 (* (- (/ 258935823777245 562949953421312)) r1))) (let ((.def_49 (* (- (/ 2457824257580501 9007199254740992)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (/ 3165828710815259 4503599627370496)))) (let ((.def_52 (or b3 .def_51 .def_45))) (let ((.def_53 (* (- (/ 4314567453890291 4503599627370496)) r3))) (let ((.def_54 (* (- (/ 1135227304405189 9007199254740992)) r2))) (let ((.def_55 (* (/ 3897929340605225 4503599627370496) r1))) (let ((.def_56 (* (/ 212891735523885 1125899906842624) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 449428735557203 2251799813685248)))) (let ((.def_59 (* (/ 5664915710797171 4503599627370496) r3))) (let ((.def_60 (* (- (/ 4771271900532945 2251799813685248)) r2))) (let ((.def_61 (* (/ 175169478208767 2251799813685248) r1))) (let ((.def_62 (* (- (/ 975124429922583 2251799813685248)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (- (/ 6712427962442859 9007199254740992))))) (let ((.def_65 (not b0))) (let ((.def_66 (or .def_65 .def_64 .def_58))) (let ((.def_67 (* (- (/ 317168404090943 2251799813685248)) r3))) (let ((.def_68 (* (- (/ 557134341770301 2251799813685248)) r2))) (let ((.def_69 (* (- (/ 16181551621631 281474976710656)) r1))) (let ((.def_70 (* (/ 948375415948031 2251799813685248) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 735804244114787 4503599627370496)))) (let ((.def_73 (* (- (/ 8969071728243329 9007199254740992)) r3))) (let ((.def_74 (* (- (/ 6267900493223997 2251799813685248)) r2))) (let ((.def_75 (* (- (/ 6085624191770649 2251799813685248)) r1))) (let ((.def_76 (* (- (/ 2398008507476831 4503599627370496)) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 8085350924313361 2251799813685248))))) (let ((.def_79 (not b2))) (let ((.def_80 (or .def_79 .def_78 .def_72))) (let ((.def_81 (* (- (/ 1063518164608663 4503599627370496)) r3))) (let ((.def_82 (* (/ 65743583772857 140737488355328) r2))) (let ((.def_83 (* (- (/ 4458431357532281 4503599627370496)) r1))) (let ((.def_84 (* (- (/ 1227800654137523 4503599627370496)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (- (/ 42876792042189 2251799813685248))))) (let ((.def_87 (* (- (/ 3462902590977171 2251799813685248)) r3))) (let ((.def_88 (* (/ 5336083729977335 2251799813685248) r2))) (let ((.def_89 (* (/ 2657095984278243 4503599627370496) r1))) (let ((.def_90 (* (/ 2996302640951471 2251799813685248) r0))) (let ((.def_91 (+ .def_90 .def_89 .def_88 .def_87))) (let ((.def_92 (<= .def_91 (/ 792263057166507 562949953421312)))) (let ((.def_93 (or .def_65 .def_92 .def_86))) (let ((.def_94 (* (/ 5390638957487497 4503599627370496) r3))) (let ((.def_95 (* (- (/ 7912322638162121 9007199254740992)) r2))) (let ((.def_96 (* (/ 1924791111429903 4503599627370496) r1))) (let ((.def_97 (* (- (/ 1932408040048545 1125899906842624)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (/ 237627797639133 9007199254740992)))) (let ((.def_100 (* (- (/ 6812347549140397 4503599627370496)) r3))) (let ((.def_101 (* (/ 2572543225610555 4503599627370496) r2))) (let ((.def_102 (* (/ 3373277233250429 4503599627370496) r1))) (let ((.def_103 (* (- (/ 124692933026697 4503599627370496)) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (- (/ 2236877773769759 9007199254740992))))) (let ((.def_106 (or .def_65 .def_105 .def_99))) (let ((.def_107 (* (/ 1726190903810399 2251799813685248) r3))) (let ((.def_108 (* (/ 622979940259195 1125899906842624) r2))) (let ((.def_109 (* (- (/ 6837730674347101 9007199254740992)) r1))) (let ((.def_110 (* (/ 1060296561938503 4503599627370496) r0))) (let ((.def_111 (+ .def_110 .def_109 .def_108 .def_107))) (let ((.def_112 (<= .def_111 (/ 570693465508015 1125899906842624)))) (let ((.def_113 (* (- (/ 61864729890175 2251799813685248)) r3))) (let ((.def_114 (* (- (/ 7566364732399387 4503599627370496)) r2))) (let ((.def_115 (* (/ 5478078530745597 2251799813685248) r1))) (let ((.def_116 (* (- (/ 1619861128950497 1125899906842624)) r0))) (let ((.def_117 (+ .def_116 .def_115 .def_114 .def_113))) (let ((.def_118 (<= .def_117 (- (/ 1381364911871059 2251799813685248))))) (let ((.def_119 (or b2 .def_118 .def_112))) (let ((.def_120 (* (- (/ 587542706105223 4503599627370496)) r3))) (let ((.def_121 (* (- (/ 504695043524605 2251799813685248)) r2))) (let ((.def_122 (* (/ 5326267373253039 9007199254740992) r1))) (let ((.def_123 (* (/ 8041093390657423 9007199254740992) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (/ 7931839029697213 9007199254740992)))) (let ((.def_126 (* (- (/ 6446360062024339 2251799813685248)) r3))) (let ((.def_127 (* (/ 4752937613046415 1125899906842624) r2))) (let ((.def_128 (* (- (/ 32377006119409 2251799813685248)) r1))) (let ((.def_129 (* (- (/ 3150645508223703 9007199254740992)) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (/ 5100965596362133 9007199254740992)))) (let ((.def_132 (or .def_12 .def_131 .def_125))) (let ((.def_133 (* (- (/ 72144774994757 140737488355328)) r3))) (let ((.def_134 (* (- (/ 3923972413297145 2251799813685248)) r2))) (let ((.def_135 (* (- (/ 4368427283077699 4503599627370496)) r1))) (let ((.def_136 (* (/ 2655898944862509 9007199254740992) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 3259217841178437 4503599627370496))))) (let ((.def_139 (* (/ 148281033432109 562949953421312) r3))) (let ((.def_140 (* (- (/ 748873163657525 2251799813685248)) r2))) (let ((.def_141 (* (- (/ 1430186793984165 2251799813685248)) r1))) (let ((.def_142 (* (/ 5156247074420171 9007199254740992) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (- (/ 390549394402905 4503599627370496))))) (let ((.def_145 (or b3 .def_144 .def_138))) (let ((.def_146 (* (- (/ 3578281432656807 2251799813685248)) r3))) (let ((.def_147 (* (/ 2112153847480349 2251799813685248) r2))) (let ((.def_148 (* (/ 5016957258296897 9007199254740992) r1))) (let ((.def_149 (* (/ 154344539140619 2251799813685248) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 3747642074920355 4503599627370496)))) (let ((.def_152 (* (- (/ 3089332490308779 2251799813685248)) r3))) (let ((.def_153 (* (/ 3535296164907611 4503599627370496) r2))) (let ((.def_154 (* (- (/ 1315517204965639 4503599627370496)) r1))) (let ((.def_155 (* (/ 3506467704091761 2251799813685248) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (/ 3008996835933357 9007199254740992)))) (let ((.def_158 (or .def_79 .def_157 .def_151))) (let ((.def_159 (* (- (/ 2212560501182569 2251799813685248)) r3))) (let ((.def_160 (* (- (/ 5181756351944711 9007199254740992)) r2))) (let ((.def_161 (* (/ 1045648549882031 2251799813685248) r1))) (let ((.def_162 (* (- (/ 2151015770935453 2251799813685248)) r0))) (let ((.def_163 (+ .def_162 .def_161 .def_160 .def_159))) (let ((.def_164 (<= .def_163 (- (/ 2583693945492365 4503599627370496))))) (let ((.def_165 (* (/ 8669923872318913 9007199254740992) r3))) (let ((.def_166 (* (- (/ 5908476937402373 4503599627370496)) r2))) (let ((.def_167 (* (- (/ 2407576797856273 9007199254740992)) r1))) (let ((.def_168 (* (/ 1821105180623701 4503599627370496) r0))) (let ((.def_169 (+ .def_168 .def_167 .def_166 .def_165))) (let ((.def_170 (<= .def_169 (- (/ 1532911634121677 9007199254740992))))) (let ((.def_171 (or .def_65 .def_170 .def_164))) (let ((.def_172 (* (/ 2427719034488613 2251799813685248) r3))) (let ((.def_173 (* (- (/ 1393768034097461 2251799813685248)) r2))) (let ((.def_174 (* (- (/ 71623020204939 281474976710656)) r1))) (let ((.def_175 (* (/ 3557342905197337 4503599627370496) r0))) (let ((.def_176 (+ .def_175 .def_174 .def_173 .def_172))) (let ((.def_177 (<= .def_176 (/ 240201914265407 281474976710656)))) (let ((.def_178 (* (/ 2168383585508985 9007199254740992) r3))) (let ((.def_179 (* (/ 3400227530981711 2251799813685248) r2))) (let ((.def_180 (* (/ 4912795451363521 4503599627370496) r1))) (let ((.def_181 (* (- (/ 2693189800218855 4503599627370496)) r0))) (let ((.def_182 (+ .def_181 .def_180 .def_179 .def_178))) (let ((.def_183 (<= .def_182 (/ 2587986355762987 2251799813685248)))) (let ((.def_184 (or b0 .def_183 .def_177))) (let ((.def_185 (* (/ 898355081433685 2251799813685248) r3))) (let ((.def_186 (* (- (/ 1964168702747503 4503599627370496)) r2))) (let ((.def_187 (* (- (/ 6819472034347611 4503599627370496)) r1))) (let ((.def_188 (* (- (/ 316110748368091 281474976710656)) r0))) (let ((.def_189 (+ .def_188 .def_187 .def_186 .def_185))) (let ((.def_190 (<= .def_189 (- (/ 5723203093546715 9007199254740992))))) (let ((.def_191 (* (/ 490412785018211 562949953421312) r3))) (let ((.def_192 (* (/ 1321506481764015 2251799813685248) r2))) (let ((.def_193 (* (/ 4578968342837963 9007199254740992) r1))) (let ((.def_194 (* (- (/ 3034790372366517 4503599627370496)) r0))) (let ((.def_195 (+ .def_194 .def_193 .def_192 .def_191))) (let ((.def_196 (<= .def_195 (/ 728817741571869 1125899906842624)))) (let ((.def_197 (or b0 .def_196 .def_190))) (let ((.def_198 (* (- (/ 591911910532657 562949953421312)) r3))) (let ((.def_199 (* (- (/ 5593158812238109 9007199254740992)) r2))) (let ((.def_200 (* (/ 1059251212782441 9007199254740992) r1))) (let ((.def_201 (* (- (/ 625081833552709 4503599627370496)) r0))) (let ((.def_202 (+ .def_201 .def_200 .def_199 .def_198))) (let ((.def_203 (<= .def_202 (- (/ 1741313426094931 4503599627370496))))) (let ((.def_204 (* (/ 2326091006488661 2251799813685248) r3))) (let ((.def_205 (* (- (/ 923052468409449 4503599627370496)) r2))) (let ((.def_206 (* (/ 79015815005127 2251799813685248) r1))) (let ((.def_207 (* (- (/ 3071088286826605 2251799813685248)) r0))) (let ((.def_208 (+ .def_207 .def_206 .def_205 .def_204))) (let ((.def_209 (<= .def_208 (- (/ 1172280814685831 4503599627370496))))) (let ((.def_210 (or b1 .def_209 .def_203))) (let ((.def_211 (* (- (/ 3885529833271865 9007199254740992)) r3))) (let ((.def_212 (* (- (/ 2543379255895417 1125899906842624)) r2))) (let ((.def_213 (* (/ 479028155553113 9007199254740992) r1))) (let ((.def_214 (* (/ 2015095147783237 2251799813685248) r0))) (let ((.def_215 (+ .def_214 .def_213 .def_212 .def_211))) (let ((.def_216 (<= .def_215 (- (/ 49434567047623 9007199254740992))))) (let ((.def_217 (* (/ 8230443720531483 9007199254740992) r3))) (let ((.def_218 (* (/ 359056596065647 281474976710656) r2))) (let ((.def_219 (* (- (/ 1686957069879309 1125899906842624)) r1))) (let ((.def_220 (* (/ 2911193597175933 1125899906842624) r0))) (let ((.def_221 (+ .def_220 .def_219 .def_218 .def_217))) (let ((.def_222 (<= .def_221 (/ 7699715855621467 4503599627370496)))) (let ((.def_223 (or b0 .def_222 .def_216))) (let ((.def_224 (* (/ 392524934971701 562949953421312) r3))) (let ((.def_225 (* (- (/ 1405289137506905 1125899906842624)) r2))) (let ((.def_226 (* (- (/ 2223574614143383 4503599627370496)) r1))) (let ((.def_227 (* (/ 3162660922061577 4503599627370496) r0))) (let ((.def_228 (+ .def_227 .def_226 .def_225 .def_224))) (let ((.def_229 (<= .def_228 (/ 2146248841046837 4503599627370496)))) (let ((.def_230 (* (- (/ 4193275075235897 4503599627370496)) r3))) (let ((.def_231 (* (- (/ 4012612913509675 2251799813685248)) r2))) (let ((.def_232 (* (/ 3972079202058985 2251799813685248) r1))) (let ((.def_233 (* (- (/ 1697123065714679 9007199254740992)) r0))) (let ((.def_234 (+ .def_233 .def_232 .def_231 .def_230))) (let ((.def_235 (<= .def_234 (- (/ 2992420777439499 4503599627370496))))) (let ((.def_236 (not b3))) (let ((.def_237 (or .def_236 .def_235 .def_229))) (let ((.def_238 (and .def_237 .def_223 .def_210 .def_197 .def_184 .def_171 .def_158 .def_145 .def_132 .def_119 .def_106 .def_93 .def_80 .def_66 .def_52 .def_39 .def_26 .def_13))) .def_238))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
