(set-logic QF_LRA)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 1643940183489079 2251799813685248) r3))) (let ((.def_1 (* (- (/ 10525001738203 17592186044416)) r2))) (let ((.def_2 (* (/ 132532190034657 4503599627370496) r1))) (let ((.def_3 (* (- (/ 775200286142421 4503599627370496)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 1645821992797077 9007199254740992)))) (let ((.def_6 (* (- (/ 2853537847596413 4503599627370496)) r3))) (let ((.def_7 (* (- (/ 5425760192418657 9007199254740992)) r2))) (let ((.def_8 (* (/ 425117614688249 1125899906842624) r1))) (let ((.def_9 (* (- (/ 172084762075151 562949953421312)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 1416425921229073 2251799813685248))))) (let ((.def_12 (not b1))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 2471654688306115 1125899906842624)) r3))) (let ((.def_15 (* (/ 2448709908897977 4503599627370496) r2))) (let ((.def_16 (* (- (/ 5402588623673945 9007199254740992)) r1))) (let ((.def_17 (* (- (/ 1724756626031103 2251799813685248)) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 2737314482629511 4503599627370496))))) (let ((.def_20 (* (- (/ 1506955064329019 9007199254740992)) r3))) (let ((.def_21 (* (- (/ 1829364235491467 4503599627370496)) r2))) (let ((.def_22 (* (- (/ 7058384890943095 9007199254740992)) r1))) (let ((.def_23 (* (/ 1930787550804037 9007199254740992) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (- (/ 1425475003430215 2251799813685248))))) (let ((.def_26 (or b2 .def_25 .def_19))) (let ((.def_27 (* (/ 666752006599179 2251799813685248) r3))) (let ((.def_28 (* (/ 5433450171486303 9007199254740992) r2))) (let ((.def_29 (* (- (/ 7676341350355457 9007199254740992)) r1))) (let ((.def_30 (* (- (/ 25954714092819 281474976710656)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (/ 618005672691981 2251799813685248)))) (let ((.def_33 (* (/ 844175521193927 281474976710656) r3))) (let ((.def_34 (* (/ 1520629650988455 4503599627370496) r2))) (let ((.def_35 (* (- (/ 1756935488617299 9007199254740992)) r1))) (let ((.def_36 (* (- (/ 2443485072720783 2251799813685248)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (/ 3141990204815343 4503599627370496)))) (let ((.def_39 (not b3))) (let ((.def_40 (or .def_39 .def_38 .def_32))) (let ((.def_41 (* (/ 3540978999968373 9007199254740992) r3))) (let ((.def_42 (* (- (/ 2751969777658723 2251799813685248)) r2))) (let ((.def_43 (* (- (/ 162973711524845 2251799813685248)) r1))) (let ((.def_44 (* (/ 1563850118295403 1125899906842624) r0))) (let ((.def_45 (+ .def_44 .def_43 .def_42 .def_41))) (let ((.def_46 (<= .def_45 (/ 1954690752723547 4503599627370496)))) (let ((.def_47 (* (/ 2306161873831339 9007199254740992) r3))) (let ((.def_48 (* (/ 4184504863273861 9007199254740992) r2))) (let ((.def_49 (* (- (/ 5620021520763267 9007199254740992)) r1))) (let ((.def_50 (* (- (/ 1161388715104469 1125899906842624)) r0))) (let ((.def_51 (+ .def_50 .def_49 .def_48 .def_47))) (let ((.def_52 (<= .def_51 (- (/ 1219937030191437 2251799813685248))))) (let ((.def_53 (or .def_39 .def_52 .def_46))) (let ((.def_54 (* (- (/ 7626717337508105 9007199254740992)) r3))) (let ((.def_55 (* (- (/ 2426764122764877 4503599627370496)) r2))) (let ((.def_56 (* (/ 361995065619283 281474976710656) r1))) (let ((.def_57 (* (/ 1423573217991 1099511627776) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (/ 4246854974310285 4503599627370496)))) (let ((.def_60 (* (- (/ 591592125443971 9007199254740992)) r3))) (let ((.def_61 (* (/ 6692953803474655 4503599627370496) r2))) (let ((.def_62 (* (- (/ 166165328324261 1125899906842624)) r1))) (let ((.def_63 (* (- (/ 4671063427218127 4503599627370496)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 271109832442229 2251799813685248)))) (let ((.def_66 (not b0))) (let ((.def_67 (or .def_66 .def_65 .def_59))) (let ((.def_68 (* (- (/ 7391744243535389 9007199254740992)) r3))) (let ((.def_69 (* (- (/ 211920494653637 140737488355328)) r2))) (let ((.def_70 (* (/ 660183512099513 1125899906842624) r1))) (let ((.def_71 (* (/ 6859055352682439 9007199254740992) r0))) (let ((.def_72 (+ .def_71 .def_70 .def_69 .def_68))) (let ((.def_73 (<= .def_72 (/ 2666020507929521 9007199254740992)))) (let ((.def_74 (* (/ 755424358065595 9007199254740992) r3))) (let ((.def_75 (* (- (/ 4198353728466951 2251799813685248)) r2))) (let ((.def_76 (* (/ 5398554020720847 4503599627370496) r1))) (let ((.def_77 (* (/ 3957345235514845 4503599627370496) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (/ 261780707004903 4503599627370496)))) (let ((.def_80 (or b1 .def_79 .def_73))) (let ((.def_81 (* (/ 297389442639557 281474976710656) r3))) (let ((.def_82 (* (- (/ 478002062651233 562949953421312)) r2))) (let ((.def_83 (* (/ 917762488073075 1125899906842624) r1))) (let ((.def_84 (* (- (/ 2009112628039745 2251799813685248)) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 1329256923053271 4503599627370496)))) (let ((.def_87 (* (- (/ 1671756376609389 1125899906842624)) r3))) (let ((.def_88 (* (/ 1468406865095167 1125899906842624) r2))) (let ((.def_89 (* (- (/ 5877706362941223 9007199254740992)) r1))) (let ((.def_90 (* (- (/ 1061716428132587 1125899906842624)) r0))) (let ((.def_91 (+ .def_90 .def_89 .def_88 .def_87))) (let ((.def_92 (<= .def_91 (- (/ 8316151862402263 9007199254740992))))) (let ((.def_93 (or .def_39 .def_92 .def_86))) (let ((.def_94 (* (/ 2551734542343235 4503599627370496) r3))) (let ((.def_95 (* (- (/ 3183577064143387 2251799813685248)) r2))) (let ((.def_96 (* (/ 2545956283831085 9007199254740992) r1))) (let ((.def_97 (* (/ 88739002456995 9007199254740992) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (/ 1320663966010707 4503599627370496)))) (let ((.def_100 (* (- (/ 2604517137790779 2251799813685248)) r3))) (let ((.def_101 (* (- (/ 4692350866611489 9007199254740992)) r2))) (let ((.def_102 (* (/ 3029729204075945 4503599627370496) r1))) (let ((.def_103 (* (- (/ 339705924786995 4503599627370496)) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (- (/ 2393974780537879 4503599627370496))))) (let ((.def_106 (or b0 .def_105 .def_99))) (let ((.def_107 (* (- (/ 3356265286016405 4503599627370496)) r3))) (let ((.def_108 (* (/ 2911921196447003 4503599627370496) r2))) (let ((.def_109 (* (/ 708754531314645 4503599627370496) r1))) (let ((.def_110 (* (- (/ 2631675520813275 2251799813685248)) r0))) (let ((.def_111 (+ .def_110 .def_109 .def_108 .def_107))) (let ((.def_112 (<= .def_111 (/ 223472151886159 9007199254740992)))) (let ((.def_113 (* (- (/ 615275225247171 281474976710656)) r3))) (let ((.def_114 (* (/ 3144792985608501 9007199254740992) r2))) (let ((.def_115 (* (/ 2614439247031961 2251799813685248) r1))) (let ((.def_116 (* (/ 83737573537903 1125899906842624) r0))) (let ((.def_117 (+ .def_116 .def_115 .def_114 .def_113))) (let ((.def_118 (<= .def_117 (- (/ 1517756632721317 4503599627370496))))) (let ((.def_119 (or b3 .def_118 .def_112))) (let ((.def_120 (* (- (/ 4111142461070697 9007199254740992)) r3))) (let ((.def_121 (* (/ 1368830639151985 2251799813685248) r2))) (let ((.def_122 (* (- (/ 1075982548902489 4503599627370496)) r1))) (let ((.def_123 (* (- (/ 1714955175291923 1125899906842624)) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (- (/ 4386005792865461 9007199254740992))))) (let ((.def_126 (* (/ 3479266919596419 9007199254740992) r3))) (let ((.def_127 (* (- (/ 7654240054825837 9007199254740992)) r2))) (let ((.def_128 (* (/ 4380623869503011 9007199254740992) r1))) (let ((.def_129 (* (- (/ 99633928372391 4503599627370496)) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (/ 14312576444089 2251799813685248)))) (let ((.def_132 (or .def_12 .def_131 .def_125))) (let ((.def_133 (* (- (/ 3842587813442855 2251799813685248)) r3))) (let ((.def_134 (* (/ 1085707127550465 4503599627370496) r2))) (let ((.def_135 (* (- (/ 9760485931715 70368744177664)) r1))) (let ((.def_136 (* (- (/ 4213631519938923 4503599627370496)) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 4041845564470189 9007199254740992))))) (let ((.def_139 (* (- (/ 1351826173240289 1125899906842624)) r3))) (let ((.def_140 (* (- (/ 6446786258557375 9007199254740992)) r2))) (let ((.def_141 (* (- (/ 6751382328493031 4503599627370496)) r1))) (let ((.def_142 (* (- (/ 207045781808187 9007199254740992)) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (- (/ 3989234883176319 2251799813685248))))) (let ((.def_145 (not b2))) (let ((.def_146 (or .def_145 .def_144 .def_138))) (let ((.def_147 (* (- (/ 6733830597568977 9007199254740992)) r3))) (let ((.def_148 (* (- (/ 5345888344880503 4503599627370496)) r2))) (let ((.def_149 (* (/ 6398105151753797 4503599627370496) r1))) (let ((.def_150 (* (- (/ 5367530845410277 4503599627370496)) r0))) (let ((.def_151 (+ .def_150 .def_149 .def_148 .def_147))) (let ((.def_152 (<= .def_151 (- (/ 1198093986282345 9007199254740992))))) (let ((.def_153 (* (- (/ 1594799752512699 9007199254740992)) r3))) (let ((.def_154 (* (- (/ 3072353827242265 4503599627370496)) r2))) (let ((.def_155 (* (- (/ 358759154591839 2251799813685248)) r1))) (let ((.def_156 (* (/ 1341570076345881 2251799813685248) r0))) (let ((.def_157 (+ .def_156 .def_155 .def_154 .def_153))) (let ((.def_158 (<= .def_157 (- (/ 2308906101740519 9007199254740992))))) (let ((.def_159 (or .def_66 .def_158 .def_152))) (let ((.def_160 (* (/ 2800989307908161 2251799813685248) r3))) (let ((.def_161 (* (- (/ 2684753346131447 9007199254740992)) r2))) (let ((.def_162 (* (- (/ 2768918728039625 2251799813685248)) r1))) (let ((.def_163 (* (/ 3174324587584667 2251799813685248) r0))) (let ((.def_164 (+ .def_163 .def_162 .def_161 .def_160))) (let ((.def_165 (<= .def_164 (/ 5918053159303671 4503599627370496)))) (let ((.def_166 (* (/ 335277567487045 562949953421312) r3))) (let ((.def_167 (* (- (/ 8500067565486321 4503599627370496)) r2))) (let ((.def_168 (* (- (/ 439168352041213 4503599627370496)) r1))) (let ((.def_169 (* (- (/ 3493031451463241 4503599627370496)) r0))) (let ((.def_170 (+ .def_169 .def_168 .def_167 .def_166))) (let ((.def_171 (<= .def_170 (- (/ 1263960070669715 1125899906842624))))) (let ((.def_172 (or b1 .def_171 .def_165))) (let ((.def_173 (* (- (/ 6640358570096655 4503599627370496)) r3))) (let ((.def_174 (* (- (/ 4336562955356431 2251799813685248)) r2))) (let ((.def_175 (* (- (/ 1517848303474821 4503599627370496)) r1))) (let ((.def_176 (* (- (/ 36464081375557 2251799813685248)) r0))) (let ((.def_177 (+ .def_176 .def_175 .def_174 .def_173))) (let ((.def_178 (<= .def_177 (- (/ 4285219842472035 4503599627370496))))) (let ((.def_179 (* (/ 3600085854291563 4503599627370496) r3))) (let ((.def_180 (* (- (/ 423115298456151 562949953421312)) r2))) (let ((.def_181 (* (- (/ 3850164719667435 4503599627370496)) r1))) (let ((.def_182 (* (- (/ 8192711401104487 9007199254740992)) r0))) (let ((.def_183 (+ .def_182 .def_181 .def_180 .def_179))) (let ((.def_184 (<= .def_183 (- (/ 4129690325847987 4503599627370496))))) (let ((.def_185 (or .def_66 .def_184 .def_178))) (let ((.def_186 (* (/ 37251821375957 140737488355328) r3))) (let ((.def_187 (* (/ 161020122328903 281474976710656) r2))) (let ((.def_188 (* (- (/ 4206707894070199 4503599627370496)) r1))) (let ((.def_189 (* (/ 194404484744905 2251799813685248) r0))) (let ((.def_190 (+ .def_189 .def_188 .def_187 .def_186))) (let ((.def_191 (<= .def_190 (/ 1965903199132821 4503599627370496)))) (let ((.def_192 (* (/ 4331592948962161 4503599627370496) r3))) (let ((.def_193 (* (/ 5369573172372071 9007199254740992) r2))) (let ((.def_194 (* (- (/ 4482619456582157 2251799813685248)) r1))) (let ((.def_195 (* (- (/ 37957543034721 1125899906842624)) r0))) (let ((.def_196 (+ .def_195 .def_194 .def_193 .def_192))) (let ((.def_197 (<= .def_196 (- (/ 395969124358935 1125899906842624))))) (let ((.def_198 (or b0 .def_197 .def_191))) (let ((.def_199 (* (- (/ 2730624126050885 9007199254740992)) r3))) (let ((.def_200 (* (- (/ 4052213540549779 4503599627370496)) r2))) (let ((.def_201 (* (/ 439154784179427 2251799813685248) r1))) (let ((.def_202 (* (/ 1495265793015859 9007199254740992) r0))) (let ((.def_203 (+ .def_202 .def_201 .def_200 .def_199))) (let ((.def_204 (<= .def_203 (- (/ 294960247445967 4503599627370496))))) (let ((.def_205 (* (/ 5449611321398663 4503599627370496) r3))) (let ((.def_206 (* (- (/ 8845811167277683 9007199254740992)) r2))) (let ((.def_207 (* (- (/ 6643605246970917 2251799813685248)) r1))) (let ((.def_208 (* (- (/ 1520125746662993 2251799813685248)) r0))) (let ((.def_209 (+ .def_208 .def_207 .def_206 .def_205))) (let ((.def_210 (<= .def_209 (- (/ 4366523447905123 2251799813685248))))) (let ((.def_211 (or b3 .def_210 .def_204))) (let ((.def_212 (* (/ 110418618855959 70368744177664) r3))) (let ((.def_213 (* (/ 399270962728599 562949953421312) r2))) (let ((.def_214 (* (- (/ 3805797387095969 2251799813685248)) r1))) (let ((.def_215 (* (/ 834766252617913 9007199254740992) r0))) (let ((.def_216 (+ .def_215 .def_214 .def_213 .def_212))) (let ((.def_217 (<= .def_216 (/ 1584063431914431 1125899906842624)))) (let ((.def_218 (* (/ 3228586535291685 9007199254740992) r3))) (let ((.def_219 (* (/ 1330312745411485 1125899906842624) r2))) (let ((.def_220 (* (- (/ 240172129766799 9007199254740992)) r1))) (let ((.def_221 (* (- (/ 1543497930280119 4503599627370496)) r0))) (let ((.def_222 (+ .def_221 .def_220 .def_219 .def_218))) (let ((.def_223 (<= .def_222 (/ 4662964099594457 9007199254740992)))) (let ((.def_224 (or .def_12 .def_223 .def_217))) (let ((.def_225 (and .def_224 .def_211 .def_198 .def_185 .def_172 .def_159 .def_146 .def_132 .def_119 .def_106 .def_93 .def_80 .def_67 .def_53 .def_40 .def_26 .def_13))) .def_225)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)