(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b2 () Bool)
(declare-fun b3 () Bool)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (- (/ 1312364050603895 1125899906842624)) r3))) (let ((.def_1 (* (/ 859442375140817 1125899906842624) r2))) (let ((.def_2 (* (/ 2385751797327363 2251799813685248) r1))) (let ((.def_3 (* (- (/ 2184081179302505 2251799813685248)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 10229180677419 1125899906842624))))) (let ((.def_6 (* (- (/ 2934635505219427 4503599627370496)) r3))) (let ((.def_7 (* (/ 5315159666204897 4503599627370496) r2))) (let ((.def_8 (* (- (/ 48364976226379 140737488355328)) r1))) (let ((.def_9 (* (/ 1534417642641875 4503599627370496) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (/ 588897757573015 4503599627370496)))) (let ((.def_12 (not b0))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 3599911757895923 4503599627370496)) r3))) (let ((.def_15 (* (/ 1031347185179871 9007199254740992) r2))) (let ((.def_16 (* (/ 3085727664801457 2251799813685248) r1))) (let ((.def_17 (* (- (/ 3334266803887325 9007199254740992)) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (/ 150092301232251 562949953421312)))) (let ((.def_20 (* (/ 709164247166151 4503599627370496) r3))) (let ((.def_21 (* (- (/ 190798962068331 4503599627370496)) r2))) (let ((.def_22 (* (- (/ 73621424263967 1125899906842624)) r1))) (let ((.def_23 (* (/ 522406607418579 562949953421312) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 1306120394090063 2251799813685248)))) (let ((.def_26 (or b2 .def_25 .def_19))) (let ((.def_27 (* (/ 7156157591356653 9007199254740992) r3))) (let ((.def_28 (* (/ 5592808199777791 9007199254740992) r2))) (let ((.def_29 (* (/ 1822160857927033 2251799813685248) r1))) (let ((.def_30 (* (- (/ 1012741865282109 1125899906842624)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 1322563476581967 1125899906842624)))) (let ((.def_33 (* (- (/ 221884965279021 4503599627370496)) r3))) (let ((.def_34 (* (/ 8841772506507159 9007199254740992) r2))) (let ((.def_35 (* (- (/ 1450800206568661 1125899906842624)) r1))) (let ((.def_36 (* (- (/ 1742535247537641 1125899906842624)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 2486092582383995 2251799813685248))))) (let ((.def_39 (or .def_12 .def_38 .def_32))) (let ((.def_40 (* (/ 805297661169809 4503599627370496) r3))) (let ((.def_41 (* (- (/ 2797130043241299 1125899906842624)) r2))) (let ((.def_42 (* (- (/ 91202184111929 2251799813685248)) r1))) (let ((.def_43 (* (- (/ 298732228320825 562949953421312)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (- (/ 3195997987212981 4503599627370496))))) (let ((.def_46 (* (/ 2721425426937031 1125899906842624) r3))) (let ((.def_47 (* (/ 3690896067024111 4503599627370496) r2))) (let ((.def_48 (* (/ 3832700388238619 9007199254740992) r1))) (let ((.def_49 (* (- (/ 6532872295836095 4503599627370496)) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (/ 1457699598149805 1125899906842624)))) (let ((.def_52 (or b2 .def_51 .def_45))) (let ((.def_53 (* (- (/ 1527481770084279 4503599627370496)) r3))) (let ((.def_54 (* (- (/ 521918502454979 2251799813685248)) r2))) (let ((.def_55 (* (/ 2699913280507093 4503599627370496) r1))) (let ((.def_56 (* (- (/ 35951998658495 281474976710656)) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 101490606416815 562949953421312)))) (let ((.def_59 (* (- (/ 2111443563236489 9007199254740992)) r3))) (let ((.def_60 (* (/ 2918035412242275 4503599627370496) r2))) (let ((.def_61 (* (/ 1677164853567699 1125899906842624) r1))) (let ((.def_62 (* (- (/ 110069240225667 35184372088832)) r0))) (let ((.def_63 (+ .def_62 .def_61 .def_60 .def_59))) (let ((.def_64 (<= .def_63 (- (/ 6617995314371479 9007199254740992))))) (let ((.def_65 (not b2))) (let ((.def_66 (or .def_65 .def_64 .def_58))) (let ((.def_67 (* (- (/ 930740313269691 1125899906842624)) r3))) (let ((.def_68 (* (/ 923279971609931 1125899906842624) r2))) (let ((.def_69 (* (/ 2755274901242965 9007199254740992) r1))) (let ((.def_70 (* (/ 2156269012919147 9007199254740992) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 1891122582873771 4503599627370496)))) (let ((.def_73 (* (/ 3533593709676933 9007199254740992) r3))) (let ((.def_74 (* (/ 892337266645139 2251799813685248) r2))) (let ((.def_75 (* (- (/ 5763105328624723 9007199254740992)) r1))) (let ((.def_76 (* (- (/ 2137968852602861 1125899906842624)) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (- (/ 8774532314326555 9007199254740992))))) (let ((.def_79 (or b2 .def_78 .def_72))) (let ((.def_80 (* (- (/ 3129808215855417 2251799813685248)) r3))) (let ((.def_81 (* (/ 2265005058304067 4503599627370496) r2))) (let ((.def_82 (* (- (/ 1891495083294095 1125899906842624)) r1))) (let ((.def_83 (* (- (/ 1519763605911927 1125899906842624)) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (- (/ 2317305124739045 2251799813685248))))) (let ((.def_86 (* (- (/ 145767397518037 70368744177664)) r3))) (let ((.def_87 (* (/ 5574254880161469 4503599627370496) r2))) (let ((.def_88 (* (- (/ 1266759980063071 1125899906842624)) r1))) (let ((.def_89 (* (/ 4814879537117663 9007199254740992) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (- (/ 4519537274023207 4503599627370496))))) (let ((.def_92 (or b1 .def_91 .def_85))) (let ((.def_93 (* (- (/ 216657173787169 562949953421312)) r3))) (let ((.def_94 (* (- (/ 1728492978899979 4503599627370496)) r2))) (let ((.def_95 (* (- (/ 2923275361508065 2251799813685248)) r1))) (let ((.def_96 (* (/ 2330390839747481 4503599627370496) r0))) (let ((.def_97 (+ .def_96 .def_95 .def_94 .def_93))) (let ((.def_98 (<= .def_97 (- (/ 1529634756883225 4503599627370496))))) (let ((.def_99 (* (- (/ 2408845515278363 4503599627370496)) r3))) (let ((.def_100 (* (- (/ 1364586740461629 4503599627370496)) r2))) (let ((.def_101 (* (/ 565209223298981 1125899906842624) r1))) (let ((.def_102 (* (- (/ 736235700467457 4503599627370496)) r0))) (let ((.def_103 (+ .def_102 .def_101 .def_100 .def_99))) (let ((.def_104 (<= .def_103 (- (/ 2627757772869111 9007199254740992))))) (let ((.def_105 (or b1 .def_104 .def_98))) (let ((.def_106 (* (- (/ 907884035481651 1125899906842624)) r3))) (let ((.def_107 (* (- (/ 292329045443917 1125899906842624)) r2))) (let ((.def_108 (* (/ 1621764626888415 2251799813685248) r1))) (let ((.def_109 (* (/ 2976169899441089 4503599627370496) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (/ 790219440548281 4503599627370496)))) (let ((.def_112 (* (/ 616416160214571 281474976710656) r3))) (let ((.def_113 (* (- (/ 465695568478963 4503599627370496)) r2))) (let ((.def_114 (* (- (/ 386709987617749 140737488355328)) r1))) (let ((.def_115 (* (- (/ 1707236434518481 9007199254740992)) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (- (/ 2407402964478871 9007199254740992))))) (let ((.def_118 (or .def_65 .def_117 .def_111))) (let ((.def_119 (* (- (/ 3134235535522803 2251799813685248)) r3))) (let ((.def_120 (* (- (/ 4343607414308725 4503599627370496)) r2))) (let ((.def_121 (* (/ 5037145325094009 9007199254740992) r1))) (let ((.def_122 (* (/ 1302427137400019 9007199254740992) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (- (/ 697731998247427 4503599627370496))))) (let ((.def_125 (* (- (/ 2345437086369031 1125899906842624)) r3))) (let ((.def_126 (* (- (/ 2379224642118101 2251799813685248)) r2))) (let ((.def_127 (* (/ 6436909101643851 9007199254740992) r1))) (let ((.def_128 (* (- (/ 4493318659592861 9007199254740992)) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (- (/ 7829950064888879 4503599627370496))))) (let ((.def_131 (not b1))) (let ((.def_132 (or .def_131 .def_130 .def_124))) (let ((.def_133 (* (- (/ 2153473117715139 1125899906842624)) r3))) (let ((.def_134 (* (/ 728465184623371 4503599627370496) r2))) (let ((.def_135 (* (/ 538941035020253 4503599627370496) r1))) (let ((.def_136 (* (/ 1247603477074377 4503599627370496) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 326693488001547 2251799813685248))))) (let ((.def_139 (* (/ 561393883402101 1125899906842624) r3))) (let ((.def_140 (* (/ 2655829261174067 2251799813685248) r2))) (let ((.def_141 (* (/ 2798443493887071 9007199254740992) r1))) (let ((.def_142 (* (- (/ 617209997462311 1125899906842624)) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (/ 6123477669410685 9007199254740992)))) (let ((.def_145 (or b3 .def_144 .def_138))) (let ((.def_146 (* (- (/ 1361522411309911 1125899906842624)) r3))) (let ((.def_147 (* (/ 832393168264563 9007199254740992) r2))) (let ((.def_148 (* (/ 1556578933907657 2251799813685248) r1))) (let ((.def_149 (* (/ 662330626692167 9007199254740992) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 109605901996011 281474976710656)))) (let ((.def_152 (* (- (/ 6041196316767339 9007199254740992)) r3))) (let ((.def_153 (* (/ 486444839746663 1125899906842624) r2))) (let ((.def_154 (* (/ 9457855327753 1125899906842624) r1))) (let ((.def_155 (* (- (/ 1321532194580113 2251799813685248)) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (- (/ 4156325954054119 9007199254740992))))) (let ((.def_158 (not b3))) (let ((.def_159 (or .def_158 .def_157 .def_151))) (let ((.def_160 (* (- (/ 1077637436838123 4503599627370496)) r3))) (let ((.def_161 (* (/ 6797910022402597 4503599627370496) r2))) (let ((.def_162 (* (/ 333070539246159 4503599627370496) r1))) (let ((.def_163 (* (- (/ 2986359638876017 9007199254740992)) r0))) (let ((.def_164 (+ .def_163 .def_162 .def_161 .def_160))) (let ((.def_165 (<= .def_164 (/ 5322020207016321 4503599627370496)))) (let ((.def_166 (* (- (/ 3376281499942345 1125899906842624)) r3))) (let ((.def_167 (* (/ 7807441103492693 4503599627370496) r2))) (let ((.def_168 (* (/ 2909189909982143 1125899906842624) r1))) (let ((.def_169 (* (- (/ 4539556368281787 9007199254740992)) r0))) (let ((.def_170 (+ .def_169 .def_168 .def_167 .def_166))) (let ((.def_171 (<= .def_170 (/ 312432559102021 2251799813685248)))) (let ((.def_172 (or .def_65 .def_171 .def_165))) (let ((.def_173 (* (- (/ 2175617870961587 2251799813685248)) r3))) (let ((.def_174 (* (- (/ 2417708637470663 4503599627370496)) r2))) (let ((.def_175 (* (- (/ 755131123348457 1125899906842624)) r1))) (let ((.def_176 (* (/ 95696190769111 562949953421312) r0))) (let ((.def_177 (+ .def_176 .def_175 .def_174 .def_173))) (let ((.def_178 (<= .def_177 (- (/ 3101865053518461 4503599627370496))))) (let ((.def_179 (* (/ 153368283331681 4503599627370496) r3))) (let ((.def_180 (* (/ 6296630176522081 4503599627370496) r2))) (let ((.def_181 (* (- (/ 1700412841175005 4503599627370496)) r1))) (let ((.def_182 (* (/ 851956618772737 9007199254740992) r0))) (let ((.def_183 (+ .def_182 .def_181 .def_180 .def_179))) (let ((.def_184 (<= .def_183 (/ 1237084342698037 2251799813685248)))) (let ((.def_185 (or .def_65 .def_184 .def_178))) (let ((.def_186 (* (- (/ 2410038211232215 2251799813685248)) r3))) (let ((.def_187 (* (/ 1995473635051757 4503599627370496) r2))) (let ((.def_188 (* (/ 6374312664142515 9007199254740992) r1))) (let ((.def_189 (* (/ 4147667766603131 4503599627370496) r0))) (let ((.def_190 (+ .def_189 .def_188 .def_187 .def_186))) (let ((.def_191 (<= .def_190 (/ 2707602598379105 2251799813685248)))) (let ((.def_192 (* (- (/ 4944572825017131 4503599627370496)) r3))) (let ((.def_193 (* (/ 1865805150142041 1125899906842624) r2))) (let ((.def_194 (* (/ 1274433714593025 4503599627370496) r1))) (let ((.def_195 (* (/ 94123754041899 2251799813685248) r0))) (let ((.def_196 (+ .def_195 .def_194 .def_193 .def_192))) (let ((.def_197 (<= .def_196 (/ 746420167393383 4503599627370496)))) (let ((.def_198 (or .def_131 .def_197 .def_191))) (let ((.def_199 (* (/ 277481838743589 9007199254740992) r3))) (let ((.def_200 (* (- (/ 5101050150924543 2251799813685248)) r2))) (let ((.def_201 (* (- (/ 154677372931071 4503599627370496)) r1))) (let ((.def_202 (* (/ 4670935691135 4503599627370496) r0))) (let ((.def_203 (+ .def_202 .def_201 .def_200 .def_199))) (let ((.def_204 (<= .def_203 (- (/ 194775046052563 1125899906842624))))) (let ((.def_205 (* (/ 4272365723854385 9007199254740992) r3))) (let ((.def_206 (* (- (/ 2443157078598513 9007199254740992)) r2))) (let ((.def_207 (* (/ 696576869157007 2251799813685248) r1))) (let ((.def_208 (* (- (/ 1728540512000445 4503599627370496)) r0))) (let ((.def_209 (+ .def_208 .def_207 .def_206 .def_205))) (let ((.def_210 (<= .def_209 (/ 445492815797049 9007199254740992)))) (let ((.def_211 (or b1 .def_210 .def_204))) (let ((.def_212 (* (- (/ 1163111602245785 562949953421312)) r3))) (let ((.def_213 (* (- (/ 2305220761874873 1125899906842624)) r2))) (let ((.def_214 (* (- (/ 6506141822698557 9007199254740992)) r1))) (let ((.def_215 (* (- (/ 2525459923004965 4503599627370496)) r0))) (let ((.def_216 (+ .def_215 .def_214 .def_213 .def_212))) (let ((.def_217 (<= .def_216 (- (/ 4879478646022339 2251799813685248))))) (let ((.def_218 (* (- (/ 3895868955370667 9007199254740992)) r3))) (let ((.def_219 (* (/ 5760651903598357 2251799813685248) r2))) (let ((.def_220 (* (/ 5122360609334937 4503599627370496) r1))) (let ((.def_221 (* (/ 1453148917006261 4503599627370496) r0))) (let ((.def_222 (+ .def_221 .def_220 .def_219 .def_218))) (let ((.def_223 (<= .def_222 (/ 3861082066294401 2251799813685248)))) (let ((.def_224 (or .def_12 .def_223 .def_217))) (let ((.def_225 (and .def_224 .def_211 .def_198 .def_185 .def_172 .def_159 .def_145 .def_132 .def_118 .def_105 .def_92 .def_79 .def_66 .def_52 .def_39 .def_26 .def_13))) .def_225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)