(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun b1 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (/ 700756987046549 2251799813685248) r3))) (let ((.def_1 (* (- (/ 2176751304753925 4503599627370496)) r2))) (let ((.def_2 (* (- (/ 1286083587592257 2251799813685248)) r1))) (let ((.def_3 (* (- (/ 2065335477805723 2251799813685248)) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 3070817880603935 4503599627370496))))) (let ((.def_6 (* (- (/ 2104004426231079 2251799813685248)) r3))) (let ((.def_7 (* (- (/ 1944746915136931 4503599627370496)) r2))) (let ((.def_8 (* (- (/ 399390410563701 562949953421312)) r1))) (let ((.def_9 (* (- (/ 3459653135313739 4503599627370496)) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 3698937377790383 2251799813685248))))) (let ((.def_12 (or b0 .def_11 .def_5))) (let ((.def_13 (* (- (/ 1128934015380321 2251799813685248)) r3))) (let ((.def_14 (* (- (/ 2133813761214037 2251799813685248)) r2))) (let ((.def_15 (* (- (/ 79915184707419 140737488355328)) r1))) (let ((.def_16 (* (/ 173971043375955 562949953421312) r0))) (let ((.def_17 (+ .def_16 .def_15 .def_14 .def_13))) (let ((.def_18 (<= .def_17 (- (/ 2275540231126691 4503599627370496))))) (let ((.def_19 (* (- (/ 2201224107659819 2251799813685248)) r3))) (let ((.def_20 (* (- (/ 1049832509266621 4503599627370496)) r2))) (let ((.def_21 (* (/ 80204438701655 9007199254740992) r1))) (let ((.def_22 (* (- (/ 93680808668803 2251799813685248)) r0))) (let ((.def_23 (+ .def_22 .def_21 .def_20 .def_19))) (let ((.def_24 (<= .def_23 (- (/ 3048042268571335 4503599627370496))))) (let ((.def_25 (or b3 .def_24 .def_18))) (let ((.def_26 (* (- (/ 900102760786253 4503599627370496)) r3))) (let ((.def_27 (* (- (/ 3987274398309777 2251799813685248)) r2))) (let ((.def_28 (* (/ 1356334900159873 2251799813685248) r1))) (let ((.def_29 (* (- (/ 870416111222993 4503599627370496)) r0))) (let ((.def_30 (+ .def_29 .def_28 .def_27 .def_26))) (let ((.def_31 (<= .def_30 (- (/ 1257380864067181 2251799813685248))))) (let ((.def_32 (* (/ 6248700570262797 9007199254740992) r3))) (let ((.def_33 (* (- (/ 1869151264007289 4503599627370496)) r2))) (let ((.def_34 (* (- (/ 7041688590327441 4503599627370496)) r1))) (let ((.def_35 (* (/ 4968964027503567 4503599627370496) r0))) (let ((.def_36 (+ .def_35 .def_34 .def_33 .def_32))) (let ((.def_37 (<= .def_36 (- (/ 956775448897723 9007199254740992))))) (let ((.def_38 (or b0 .def_37 .def_31))) (let ((.def_39 (* (/ 478518417429695 562949953421312) r3))) (let ((.def_40 (* (/ 1378799581861613 2251799813685248) r2))) (let ((.def_41 (* (- (/ 90448231722797 1125899906842624)) r1))) (let ((.def_42 (* (- (/ 4096679266016899 4503599627370496)) r0))) (let ((.def_43 (+ .def_42 .def_41 .def_40 .def_39))) (let ((.def_44 (<= .def_43 (/ 2922114392957387 4503599627370496)))) (let ((.def_45 (* (/ 3119246502426103 2251799813685248) r3))) (let ((.def_46 (* (/ 1500662252758665 1125899906842624) r2))) (let ((.def_47 (* (- (/ 1640234443453517 9007199254740992)) r1))) (let ((.def_48 (* (/ 1493043137788179 1125899906842624) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (/ 4917198752128039 2251799813685248)))) (let ((.def_51 (or b0 .def_50 .def_44))) (let ((.def_52 (* (/ 4097909823480097 4503599627370496) r3))) (let ((.def_53 (* (- (/ 2525785491020947 2251799813685248)) r2))) (let ((.def_54 (* (/ 4328095420325283 9007199254740992) r1))) (let ((.def_55 (* (/ 3632955382810043 2251799813685248) r0))) (let ((.def_56 (+ .def_55 .def_54 .def_53 .def_52))) (let ((.def_57 (<= .def_56 (/ 3760680727195817 2251799813685248)))) (let ((.def_58 (* (- (/ 3628986760422535 2251799813685248)) r3))) (let ((.def_59 (* (/ 708902612442639 4503599627370496) r2))) (let ((.def_60 (* (/ 1001882454784919 2251799813685248) r1))) (let ((.def_61 (* (/ 5667880364319395 9007199254740992) r0))) (let ((.def_62 (+ .def_61 .def_60 .def_59 .def_58))) (let ((.def_63 (<= .def_62 (- (/ 88247162013511 281474976710656))))) (let ((.def_64 (not b0))) (let ((.def_65 (or .def_64 .def_63 .def_57))) (let ((.def_66 (* (/ 1908412304210437 2251799813685248) r3))) (let ((.def_67 (* (/ 914258718437645 4503599627370496) r2))) (let ((.def_68 (* (/ 217191258200729 140737488355328) r1))) (let ((.def_69 (* (- (/ 3080030822655693 2251799813685248)) r0))) (let ((.def_70 (+ .def_69 .def_68 .def_67 .def_66))) (let ((.def_71 (<= .def_70 (/ 637460793343357 562949953421312)))) (let ((.def_72 (* (- (/ 7556965358572803 4503599627370496)) r3))) (let ((.def_73 (* (/ 3205848517569991 4503599627370496) r2))) (let ((.def_74 (* (/ 1430056488349025 4503599627370496) r1))) (let ((.def_75 (* (- (/ 2327726880706965 9007199254740992)) r0))) (let ((.def_76 (+ .def_75 .def_74 .def_73 .def_72))) (let ((.def_77 (<= .def_76 (- (/ 179945714357111 281474976710656))))) (let ((.def_78 (or .def_64 .def_77 .def_71))) (let ((.def_79 (* (- (/ 563396754963495 4503599627370496)) r3))) (let ((.def_80 (* (- (/ 7557975132797177 4503599627370496)) r2))) (let ((.def_81 (* (/ 3623151346105 70368744177664) r1))) (let ((.def_82 (* (/ 4388640103493501 4503599627370496) r0))) (let ((.def_83 (+ .def_82 .def_81 .def_80 .def_79))) (let ((.def_84 (<= .def_83 (/ 920547599910967 2251799813685248)))) (let ((.def_85 (* (/ 131634786792657 140737488355328) r3))) (let ((.def_86 (* (- (/ 1230776309177627 1125899906842624)) r2))) (let ((.def_87 (* (/ 4190437861181735 4503599627370496) r1))) (let ((.def_88 (* (- (/ 1576945020267019 2251799813685248)) r0))) (let ((.def_89 (+ .def_88 .def_87 .def_86 .def_85))) (let ((.def_90 (<= .def_89 (- (/ 382620741370065 2251799813685248))))) (let ((.def_91 (or b0 .def_90 .def_84))) (let ((.def_92 (* (- (/ 4467564301166061 9007199254740992)) r3))) (let ((.def_93 (* (/ 113639959625789 562949953421312) r2))) (let ((.def_94 (* (- (/ 58668849661099 140737488355328)) r1))) (let ((.def_95 (* (- (/ 4291065333640587 4503599627370496)) r0))) (let ((.def_96 (+ .def_95 .def_94 .def_93 .def_92))) (let ((.def_97 (<= .def_96 (- (/ 970292267895965 2251799813685248))))) (let ((.def_98 (* (- (/ 3625103917866851 2251799813685248)) r3))) (let ((.def_99 (* (- (/ 2027510054524941 4503599627370496)) r2))) (let ((.def_100 (* (/ 4341457266692439 2251799813685248) r1))) (let ((.def_101 (* (- (/ 5008244924818755 9007199254740992)) r0))) (let ((.def_102 (+ .def_101 .def_100 .def_99 .def_98))) (let ((.def_103 (<= .def_102 (- (/ 917515022260905 2251799813685248))))) (let ((.def_104 (not b1))) (let ((.def_105 (or .def_104 .def_103 .def_97))) (let ((.def_106 (* (/ 2577424593956041 2251799813685248) r3))) (let ((.def_107 (* (- (/ 2711178528281485 2251799813685248)) r2))) (let ((.def_108 (* (- (/ 1356672569490397 2251799813685248)) r1))) (let ((.def_109 (* (- (/ 2993841213892871 2251799813685248)) r0))) (let ((.def_110 (+ .def_109 .def_108 .def_107 .def_106))) (let ((.def_111 (<= .def_110 (- (/ 4001434749134465 9007199254740992))))) (let ((.def_112 (* (- (/ 1742796742534129 2251799813685248)) r3))) (let ((.def_113 (* (- (/ 252737750177067 1125899906842624)) r2))) (let ((.def_114 (* (- (/ 565136392549193 562949953421312)) r1))) (let ((.def_115 (* (- (/ 312981777060537 281474976710656)) r0))) (let ((.def_116 (+ .def_115 .def_114 .def_113 .def_112))) (let ((.def_117 (<= .def_116 (- (/ 1932389417190635 1125899906842624))))) (let ((.def_118 (or b0 .def_117 .def_111))) (let ((.def_119 (* (- (/ 3418006382484187 4503599627370496)) r3))) (let ((.def_120 (* (- (/ 289076822927927 4503599627370496)) r2))) (let ((.def_121 (* (/ 83990646700819 1125899906842624) r1))) (let ((.def_122 (* (- (/ 5126568830187163 4503599627370496)) r0))) (let ((.def_123 (+ .def_122 .def_121 .def_120 .def_119))) (let ((.def_124 (<= .def_123 (- (/ 5697152178019009 9007199254740992))))) (let ((.def_125 (* (/ 2225757346189079 4503599627370496) r3))) (let ((.def_126 (* (- (/ 2417062164528087 4503599627370496)) r2))) (let ((.def_127 (* (/ 2742102373701573 4503599627370496) r1))) (let ((.def_128 (* (- (/ 3048882538566693 4503599627370496)) r0))) (let ((.def_129 (+ .def_128 .def_127 .def_126 .def_125))) (let ((.def_130 (<= .def_129 (- (/ 1540089258695463 9007199254740992))))) (let ((.def_131 (or b1 .def_130 .def_124))) (let ((.def_132 (* (/ 1540236837596269 2251799813685248) r3))) (let ((.def_133 (* (/ 2451673811119665 4503599627370496) r2))) (let ((.def_134 (* (/ 3600514058329413 9007199254740992) r1))) (let ((.def_135 (* (- (/ 2390779528353999 2251799813685248)) r0))) (let ((.def_136 (+ .def_135 .def_134 .def_133 .def_132))) (let ((.def_137 (<= .def_136 (/ 1932277710136235 2251799813685248)))) (let ((.def_138 (* (/ 2825962566133899 2251799813685248) r3))) (let ((.def_139 (* (- (/ 41873571286227 9007199254740992)) r2))) (let ((.def_140 (* (- (/ 3295283473486819 4503599627370496)) r1))) (let ((.def_141 (* (- (/ 5178841103459143 4503599627370496)) r0))) (let ((.def_142 (+ .def_141 .def_140 .def_139 .def_138))) (let ((.def_143 (<= .def_142 (- (/ 474097555127805 1125899906842624))))) (let ((.def_144 (not b2))) (let ((.def_145 (or .def_144 .def_143 .def_137))) (let ((.def_146 (* (/ 554977107337783 562949953421312) r3))) (let ((.def_147 (* (/ 252664093777145 2251799813685248) r2))) (let ((.def_148 (* (/ 339263127919021 562949953421312) r1))) (let ((.def_149 (* (- (/ 487276564137659 562949953421312)) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 3074613847119047 4503599627370496)))) (let ((.def_152 (* (- (/ 8144541530055763 4503599627370496)) r3))) (let ((.def_153 (* (- (/ 4688615449467377 9007199254740992)) r2))) (let ((.def_154 (* (- (/ 4386963205575477 4503599627370496)) r1))) (let ((.def_155 (* (- (/ 4271803195621271 4503599627370496)) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (- (/ 2565808904248237 1125899906842624))))) (let ((.def_158 (or b1 .def_157 .def_151))) (let ((.def_159 (* (- (/ 5725919991964119 9007199254740992)) r3))) (let ((.def_160 (* (- (/ 4866284675389905 2251799813685248)) r2))) (let ((.def_161 (* (/ 395452109906617 562949953421312) r1))) (let ((.def_162 (* (/ 5706583442288367 9007199254740992) r0))) (let ((.def_163 (+ .def_162 .def_161 .def_160 .def_159))) (let ((.def_164 (<= .def_163 (/ 1998530728714725 9007199254740992)))) (let ((.def_165 (* (- (/ 5769924416982495 2251799813685248)) r3))) (let ((.def_166 (* (- (/ 917450766215469 2251799813685248)) r2))) (let ((.def_167 (* (/ 1509979415075791 4503599627370496) r1))) (let ((.def_168 (* (/ 1829769831758335 1125899906842624) r0))) (let ((.def_169 (+ .def_168 .def_167 .def_166 .def_165))) (let ((.def_170 (<= .def_169 (- (/ 1255887480230965 2251799813685248))))) (let ((.def_171 (or b2 .def_170 .def_164))) (let ((.def_172 (* (- (/ 1342851308675 562949953421312)) r3))) (let ((.def_173 (* (- (/ 1922674817274743 2251799813685248)) r2))) (let ((.def_174 (* (/ 5627089881539037 4503599627370496) r1))) (let ((.def_175 (* (/ 4145778944376285 4503599627370496) r0))) (let ((.def_176 (+ .def_175 .def_174 .def_173 .def_172))) (let ((.def_177 (<= .def_176 (/ 6807824956719835 4503599627370496)))) (let ((.def_178 (* (- (/ 9893268943741 140737488355328)) r3))) (let ((.def_179 (* (- (/ 1416026800885003 9007199254740992)) r2))) (let ((.def_180 (* (/ 6586028597947259 9007199254740992) r1))) (let ((.def_181 (* (/ 5149944913586357 4503599627370496) r0))) (let ((.def_182 (+ .def_181 .def_180 .def_179 .def_178))) (let ((.def_183 (<= .def_182 (/ 8097376152965303 9007199254740992)))) (let ((.def_184 (or b2 .def_183 .def_177))) (let ((.def_185 (* (/ 842823460189079 562949953421312) r3))) (let ((.def_186 (* (- (/ 7637843518965769 4503599627370496)) r2))) (let ((.def_187 (* (- (/ 1171210676245125 1125899906842624)) r1))) (let ((.def_188 (* (- (/ 4111647327574855 4503599627370496)) r0))) (let ((.def_189 (+ .def_188 .def_187 .def_186 .def_185))) (let ((.def_190 (<= .def_189 (/ 739229020217335 4503599627370496)))) (let ((.def_191 (* (/ 5086515389624173 4503599627370496) r3))) (let ((.def_192 (* (- (/ 8096316052251237 9007199254740992)) r2))) (let ((.def_193 (* (- (/ 170604287194675 9007199254740992)) r1))) (let ((.def_194 (* (- (/ 3734195080617457 9007199254740992)) r0))) (let ((.def_195 (+ .def_194 .def_193 .def_192 .def_191))) (let ((.def_196 (<= .def_195 (- (/ 1498683417447779 9007199254740992))))) (let ((.def_197 (or b3 .def_196 .def_190))) (let ((.def_198 (* (- (/ 1456649387712313 2251799813685248)) r3))) (let ((.def_199 (* (- (/ 5494252562549389 9007199254740992)) r2))) (let ((.def_200 (* (/ 4113872835825829 9007199254740992) r1))) (let ((.def_201 (* (- (/ 4403240097906001 4503599627370496)) r0))) (let ((.def_202 (+ .def_201 .def_200 .def_199 .def_198))) (let ((.def_203 (<= .def_202 (- (/ 4458784737283539 9007199254740992))))) (let ((.def_204 (* (- (/ 935739860802795 2251799813685248)) r3))) (let ((.def_205 (* (/ 859882240107709 281474976710656) r2))) (let ((.def_206 (* (- (/ 5703954030770511 9007199254740992)) r1))) (let ((.def_207 (* (- (/ 5284059928086267 4503599627370496)) r0))) (let ((.def_208 (+ .def_207 .def_206 .def_205 .def_204))) (let ((.def_209 (<= .def_208 (/ 3140242211547151 9007199254740992)))) (let ((.def_210 (or b1 .def_209 .def_203))) (let ((.def_211 (* (- (/ 669314586658401 2251799813685248)) r3))) (let ((.def_212 (* (- (/ 650503895702479 281474976710656)) r2))) (let ((.def_213 (* (- (/ 1059886302340865 4503599627370496)) r1))) (let ((.def_214 (* (- (/ 8749182329328439 9007199254740992)) r0))) (let ((.def_215 (+ .def_214 .def_213 .def_212 .def_211))) (let ((.def_216 (<= .def_215 (- (/ 6558142062307103 9007199254740992))))) (let ((.def_217 (* (- (/ 8013048070827617 9007199254740992)) r3))) (let ((.def_218 (* (- (/ 4997406103171049 2251799813685248)) r2))) (let ((.def_219 (* (/ 2846431139112489 2251799813685248) r1))) (let ((.def_220 (* (/ 2467539829941677 2251799813685248) r0))) (let ((.def_221 (+ .def_220 .def_219 .def_218 .def_217))) (let ((.def_222 (<= .def_221 (- (/ 4866159198578507 9007199254740992))))) (let ((.def_223 (or b3 .def_222 .def_216))) (let ((.def_224 (* (- (/ 404595027757181 1125899906842624)) r3))) (let ((.def_225 (* (/ 805189982617553 562949953421312) r2))) (let ((.def_226 (* (- (/ 7209599626750227 9007199254740992)) r1))) (let ((.def_227 (* (/ 262542827689521 2251799813685248) r0))) (let ((.def_228 (+ .def_227 .def_226 .def_225 .def_224))) (let ((.def_229 (<= .def_228 (/ 4227104442606279 4503599627370496)))) (let ((.def_230 (* (- (/ 2228383766928097 2251799813685248)) r3))) (let ((.def_231 (* (- (/ 691322083095947 2251799813685248)) r2))) (let ((.def_232 (* (- (/ 7097835281337015 4503599627370496)) r1))) (let ((.def_233 (* (/ 2791944833267123 2251799813685248) r0))) (let ((.def_234 (+ .def_233 .def_232 .def_231 .def_230))) (let ((.def_235 (<= .def_234 (- (/ 3882234047133585 4503599627370496))))) (let ((.def_236 (not b3))) (let ((.def_237 (or .def_236 .def_235 .def_229))) (let ((.def_238 (and .def_237 .def_223 .def_210 .def_197 .def_184 .def_171 .def_158 .def_145 .def_131 .def_118 .def_105 .def_91 .def_78 .def_65 .def_51 .def_38 .def_25 .def_12))) .def_238))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
