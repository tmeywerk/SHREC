(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun r0 () Real)
(declare-fun b1 () Bool)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(declare-fun b0 () Bool)
(assert (let ((.def_0 (* (- (/ 675000392992629 562949953421312)) r3))) (let ((.def_1 (* (/ 119778887002473 4503599627370496) r2))) (let ((.def_2 (* (- (/ 1157083528189747 1125899906842624)) r1))) (let ((.def_3 (* (/ 1107828882519415 1125899906842624) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (/ 778878800612269 9007199254740992)))) (let ((.def_6 (* (- (/ 804126382345379 9007199254740992)) r3))) (let ((.def_7 (* (/ 555183704406895 1125899906842624) r2))) (let ((.def_8 (* (- (/ 1389360393174295 1125899906842624)) r1))) (let ((.def_9 (* (/ 5604402207275323 9007199254740992) r0))) (let ((.def_10 (+ .def_9 .def_8 .def_7 .def_6))) (let ((.def_11 (<= .def_10 (- (/ 355981471013087 9007199254740992))))) (let ((.def_12 (not b3))) (let ((.def_13 (or .def_12 .def_11 .def_5))) (let ((.def_14 (* (- (/ 668894276727863 1125899906842624)) r3))) (let ((.def_15 (* (- (/ 1015264816134609 2251799813685248)) r2))) (let ((.def_16 (* (/ 1349949007372803 9007199254740992) r1))) (let ((.def_17 (* (- (/ 1361140520300653 2251799813685248)) r0))) (let ((.def_18 (+ .def_17 .def_16 .def_15 .def_14))) (let ((.def_19 (<= .def_18 (- (/ 175475328017131 281474976710656))))) (let ((.def_20 (* (- (/ 671590354391415 4503599627370496)) r3))) (let ((.def_21 (* (/ 2641254839218013 4503599627370496) r2))) (let ((.def_22 (* (/ 6294128746906537 4503599627370496) r1))) (let ((.def_23 (* (/ 8504175231261445 9007199254740992) r0))) (let ((.def_24 (+ .def_23 .def_22 .def_21 .def_20))) (let ((.def_25 (<= .def_24 (/ 2731394016644001 2251799813685248)))) (let ((.def_26 (or b1 .def_25 .def_19))) (let ((.def_27 (* (- (/ 3225959908362293 4503599627370496)) r3))) (let ((.def_28 (* (- (/ 2353719386927033 4503599627370496)) r2))) (let ((.def_29 (* (- (/ 2889393070792003 4503599627370496)) r1))) (let ((.def_30 (* (- (/ 264604918783973 281474976710656)) r0))) (let ((.def_31 (+ .def_30 .def_29 .def_28 .def_27))) (let ((.def_32 (<= .def_31 (- (/ 3646401125032453 4503599627370496))))) (let ((.def_33 (* (/ 56032408284555 2251799813685248) r3))) (let ((.def_34 (* (- (/ 206499612466001 4503599627370496)) r2))) (let ((.def_35 (* (/ 381233054392079 2251799813685248) r1))) (let ((.def_36 (* (- (/ 1624957232941237 1125899906842624)) r0))) (let ((.def_37 (+ .def_36 .def_35 .def_34 .def_33))) (let ((.def_38 (<= .def_37 (- (/ 1728646396503799 2251799813685248))))) (let ((.def_39 (or .def_12 .def_38 .def_32))) (let ((.def_40 (* (- (/ 901095932479407 1125899906842624)) r3))) (let ((.def_41 (* (/ 3640673260015021 4503599627370496) r2))) (let ((.def_42 (* (/ 3079119507044833 4503599627370496) r1))) (let ((.def_43 (* (- (/ 2994285187770141 4503599627370496)) r0))) (let ((.def_44 (+ .def_43 .def_42 .def_41 .def_40))) (let ((.def_45 (<= .def_44 (/ 241317187057081 562949953421312)))) (let ((.def_46 (* (- (/ 4660321281534973 2251799813685248)) r3))) (let ((.def_47 (* (- (/ 2320169939435519 9007199254740992)) r2))) (let ((.def_48 (* (- (/ 4563475253371065 9007199254740992)) r1))) (let ((.def_49 (* (/ 3620946842948671 4503599627370496) r0))) (let ((.def_50 (+ .def_49 .def_48 .def_47 .def_46))) (let ((.def_51 (<= .def_50 (- (/ 4783025768290723 4503599627370496))))) (let ((.def_52 (not b0))) (let ((.def_53 (or .def_52 .def_51 .def_45))) (let ((.def_54 (* (- (/ 5428239964779373 9007199254740992)) r3))) (let ((.def_55 (* (/ 983659182720607 4503599627370496) r2))) (let ((.def_56 (* (- (/ 684663504031563 562949953421312)) r1))) (let ((.def_57 (* (/ 7948095000412247 9007199254740992) r0))) (let ((.def_58 (+ .def_57 .def_56 .def_55 .def_54))) (let ((.def_59 (<= .def_58 (/ 2503464551522915 9007199254740992)))) (let ((.def_60 (* (/ 545312037101353 9007199254740992) r3))) (let ((.def_61 (* (/ 2779533520169381 2251799813685248) r2))) (let ((.def_62 (* (- (/ 497796999788707 1125899906842624)) r1))) (let ((.def_63 (* (/ 4136936756593075 4503599627370496) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (/ 3795601092775541 4503599627370496)))) (let ((.def_66 (or b2 .def_65 .def_59))) (let ((.def_67 (* (/ 2258990967753747 4503599627370496) r3))) (let ((.def_68 (* (- (/ 32622258111145 1125899906842624)) r2))) (let ((.def_69 (* (/ 1892821149190773 2251799813685248) r1))) (let ((.def_70 (* (/ 2406812442364583 9007199254740992) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 2530657589486961 2251799813685248)))) (let ((.def_73 (* (/ 2128251240684675 1125899906842624) r3))) (let ((.def_74 (* (- (/ 3234492976566931 2251799813685248)) r2))) (let ((.def_75 (* (- (/ 1499606515924989 1125899906842624)) r1))) (let ((.def_76 (* (/ 8336566923268941 9007199254740992) r0))) (let ((.def_77 (+ .def_76 .def_75 .def_74 .def_73))) (let ((.def_78 (<= .def_77 (/ 19090797243915 9007199254740992)))) (let ((.def_79 (or b3 .def_78 .def_72))) (let ((.def_80 (* (/ 1521298387997741 4503599627370496) r3))) (let ((.def_81 (* (- (/ 1671528360534639 4503599627370496)) r2))) (let ((.def_82 (* (/ 2044658601763059 9007199254740992) r1))) (let ((.def_83 (* (- (/ 3001374675614605 1125899906842624)) r0))) (let ((.def_84 (+ .def_83 .def_82 .def_81 .def_80))) (let ((.def_85 (<= .def_84 (- (/ 1506143144409443 4503599627370496))))) (let ((.def_86 (* (- (/ 471312910341199 562949953421312)) r3))) (let ((.def_87 (* (/ 193955037732977 70368744177664) r2))) (let ((.def_88 (* (- (/ 3146523574574455 4503599627370496)) r1))) (let ((.def_89 (* (- (/ 4498159283434185 4503599627370496)) r0))) (let ((.def_90 (+ .def_89 .def_88 .def_87 .def_86))) (let ((.def_91 (<= .def_90 (/ 741415897707761 4503599627370496)))) (let ((.def_92 (not b1))) (let ((.def_93 (or .def_92 .def_91 .def_85))) (let ((.def_94 (* (- (/ 330332669337161 140737488355328)) r3))) (let ((.def_95 (* (/ 5430050159499873 9007199254740992) r2))) (let ((.def_96 (* (- (/ 2933713110560853 9007199254740992)) r1))) (let ((.def_97 (* (- (/ 713151532681071 1125899906842624)) r0))) (let ((.def_98 (+ .def_97 .def_96 .def_95 .def_94))) (let ((.def_99 (<= .def_98 (- (/ 3318405976970879 9007199254740992))))) (let ((.def_100 (* (- (/ 5661504614365211 2251799813685248)) r3))) (let ((.def_101 (* (/ 1809823257055159 1125899906842624) r2))) (let ((.def_102 (* (- (/ 4740682393569413 9007199254740992)) r1))) (let ((.def_103 (* (/ 4325866643222093 2251799813685248) r0))) (let ((.def_104 (+ .def_103 .def_102 .def_101 .def_100))) (let ((.def_105 (<= .def_104 (/ 348759196218801 4503599627370496)))) (let ((.def_106 (or b1 .def_105 .def_99))) (let ((.def_107 (* (- (/ 4878808158803965 9007199254740992)) r3))) (let ((.def_108 (* (- (/ 1849162495230983 2251799813685248)) r2))) (let ((.def_109 (* (- (/ 2151660318077711 2251799813685248)) r1))) (let ((.def_110 (* (/ 5640984445301945 9007199254740992) r0))) (let ((.def_111 (+ .def_110 .def_109 .def_108 .def_107))) (let ((.def_112 (<= .def_111 (- (/ 4980443215460327 9007199254740992))))) (let ((.def_113 (* (/ 274779507965005 70368744177664) r3))) (let ((.def_114 (* (- (/ 4038339712247547 2251799813685248)) r2))) (let ((.def_115 (* (/ 2361699623028229 2251799813685248) r1))) (let ((.def_116 (* (- (/ 1226247653702589 562949953421312)) r0))) (let ((.def_117 (+ .def_116 .def_115 .def_114 .def_113))) (let ((.def_118 (<= .def_117 (/ 3529459508966679 9007199254740992)))) (let ((.def_119 (or .def_92 .def_118 .def_112))) (let ((.def_120 (* (- (/ 2939648806130951 9007199254740992)) r3))) (let ((.def_121 (* (- (/ 7255297815303489 9007199254740992)) r2))) (let ((.def_122 (* (- (/ 2265292322632829 4503599627370496)) r1))) (let ((.def_123 (* (/ 2169650245553003 4503599627370496) r0))) (let ((.def_124 (+ .def_123 .def_122 .def_121 .def_120))) (let ((.def_125 (<= .def_124 (- (/ 1299194793488653 4503599627370496))))) (let ((.def_126 (* (/ 2047878749093233 9007199254740992) r3))) (let ((.def_127 (* (/ 6304666266285803 9007199254740992) r2))) (let ((.def_128 (* (/ 2289466126045213 1125899906842624) r1))) (let ((.def_129 (* (/ 946404497363347 2251799813685248) r0))) (let ((.def_130 (+ .def_129 .def_128 .def_127 .def_126))) (let ((.def_131 (<= .def_130 (/ 3155006755582755 2251799813685248)))) (let ((.def_132 (or .def_52 .def_131 .def_125))) (let ((.def_133 (* (/ 610710014531481 2251799813685248) r3))) (let ((.def_134 (* (- (/ 706939170747797 562949953421312)) r2))) (let ((.def_135 (* (- (/ 728014005201751 562949953421312)) r1))) (let ((.def_136 (* (- (/ 170893110268437 9007199254740992)) r0))) (let ((.def_137 (+ .def_136 .def_135 .def_134 .def_133))) (let ((.def_138 (<= .def_137 (- (/ 5092515450226545 9007199254740992))))) (let ((.def_139 (* (/ 1054006254438687 2251799813685248) r3))) (let ((.def_140 (* (/ 651990983197211 1125899906842624) r2))) (let ((.def_141 (* (- (/ 2783953488743891 9007199254740992)) r1))) (let ((.def_142 (* (/ 8297636948412487 4503599627370496) r0))) (let ((.def_143 (+ .def_142 .def_141 .def_140 .def_139))) (let ((.def_144 (<= .def_143 (/ 3033277868728469 2251799813685248)))) (let ((.def_145 (or b0 .def_144 .def_138))) (let ((.def_146 (* (- (/ 1265099632055367 1125899906842624)) r3))) (let ((.def_147 (* (/ 2112038913290769 4503599627370496) r2))) (let ((.def_148 (* (/ 3091860619760577 4503599627370496) r1))) (let ((.def_149 (* (- (/ 47253294361495 1125899906842624)) r0))) (let ((.def_150 (+ .def_149 .def_148 .def_147 .def_146))) (let ((.def_151 (<= .def_150 (/ 1257809792707279 2251799813685248)))) (let ((.def_152 (* (/ 3161208375083405 4503599627370496) r3))) (let ((.def_153 (* (/ 1031123977344005 1125899906842624) r2))) (let ((.def_154 (* (/ 5799953586247467 4503599627370496) r1))) (let ((.def_155 (* (- (/ 3272771241883313 4503599627370496)) r0))) (let ((.def_156 (+ .def_155 .def_154 .def_153 .def_152))) (let ((.def_157 (<= .def_156 (/ 4285865654342783 4503599627370496)))) (let ((.def_158 (or .def_12 .def_157 .def_151))) (let ((.def_159 (* (- (/ 234229836272379 1125899906842624)) r3))) (let ((.def_160 (* (- (/ 236523734237981 4503599627370496)) r2))) (let ((.def_161 (* (/ 1056312993584099 4503599627370496) r1))) (let ((.def_162 (* (/ 4106976147837673 9007199254740992) r0))) (let ((.def_163 (+ .def_162 .def_161 .def_160 .def_159))) (let ((.def_164 (<= .def_163 (/ 1098860395627131 4503599627370496)))) (let ((.def_165 (* (/ 3340674939417877 9007199254740992) r3))) (let ((.def_166 (* (- (/ 3133312600615555 2251799813685248)) r2))) (let ((.def_167 (* (- (/ 898097077797895 4503599627370496)) r1))) (let ((.def_168 (* (- (/ 3726273097842543 1125899906842624)) r0))) (let ((.def_169 (+ .def_168 .def_167 .def_166 .def_165))) (let ((.def_170 (<= .def_169 (- (/ 5594199854851221 2251799813685248))))) (let ((.def_171 (or b0 .def_170 .def_164))) (let ((.def_172 (* (/ 3473102734823567 4503599627370496) r3))) (let ((.def_173 (* (- (/ 1692494901900639 2251799813685248)) r2))) (let ((.def_174 (* (/ 1524984546354257 2251799813685248) r1))) (let ((.def_175 (* (- (/ 1343991495112843 4503599627370496)) r0))) (let ((.def_176 (+ .def_175 .def_174 .def_173 .def_172))) (let ((.def_177 (<= .def_176 (/ 776842497887257 1125899906842624)))) (let ((.def_178 (* (- (/ 50259069950609 70368744177664)) r3))) (let ((.def_179 (* (/ 424312333603493 1125899906842624) r2))) (let ((.def_180 (* (/ 2540210268161527 1125899906842624) r1))) (let ((.def_181 (* (/ 2096818176585279 1125899906842624) r0))) (let ((.def_182 (+ .def_181 .def_180 .def_179 .def_178))) (let ((.def_183 (<= .def_182 (/ 7367799489120759 4503599627370496)))) (let ((.def_184 (or .def_52 .def_183 .def_177))) (let ((.def_185 (* (/ 1300465546083653 4503599627370496) r3))) (let ((.def_186 (* (- (/ 2858833988302843 4503599627370496)) r2))) (let ((.def_187 (* (/ 5995592066444659 4503599627370496) r1))) (let ((.def_188 (* (- (/ 472256666726247 562949953421312)) r0))) (let ((.def_189 (+ .def_188 .def_187 .def_186 .def_185))) (let ((.def_190 (<= .def_189 (/ 3729544051073211 4503599627370496)))) (let ((.def_191 (* (- (/ 2769672532511723 4503599627370496)) r3))) (let ((.def_192 (* (- (/ 1196993873738713 9007199254740992)) r2))) (let ((.def_193 (* (/ 346386438999419 562949953421312) r1))) (let ((.def_194 (* (- (/ 67754061991849 2251799813685248)) r0))) (let ((.def_195 (+ .def_194 .def_193 .def_192 .def_191))) (let ((.def_196 (<= .def_195 (- (/ 457347951484533 4503599627370496))))) (let ((.def_197 (or b2 .def_196 .def_190))) (let ((.def_198 (* (- (/ 400327969902831 140737488355328)) r3))) (let ((.def_199 (* (/ 472381251868353 4503599627370496) r2))) (let ((.def_200 (* (- (/ 4136221070164939 2251799813685248)) r1))) (let ((.def_201 (* (/ 4914193604173329 4503599627370496) r0))) (let ((.def_202 (+ .def_201 .def_200 .def_199 .def_198))) (let ((.def_203 (<= .def_202 (- (/ 956249884367273 1125899906842624))))) (let ((.def_204 (* (- (/ 2365371006423979 9007199254740992)) r3))) (let ((.def_205 (* (- (/ 8749927840007179 9007199254740992)) r2))) (let ((.def_206 (* (/ 2696944111731761 1125899906842624) r1))) (let ((.def_207 (* (- (/ 3497714415760475 2251799813685248)) r0))) (let ((.def_208 (+ .def_207 .def_206 .def_205 .def_204))) (let ((.def_209 (<= .def_208 (- (/ 2704380616864819 9007199254740992))))) (let ((.def_210 (or b3 .def_209 .def_203))) (let ((.def_211 (* (/ 326264036966819 4503599627370496) r3))) (let ((.def_212 (* (/ 1845827424255425 2251799813685248) r2))) (let ((.def_213 (* (/ 3599486174339085 2251799813685248) r1))) (let ((.def_214 (* (- (/ 759211514943887 562949953421312)) r0))) (let ((.def_215 (+ .def_214 .def_213 .def_212 .def_211))) (let ((.def_216 (<= .def_215 (/ 3025999681841675 2251799813685248)))) (let ((.def_217 (* (/ 2572332367894777 4503599627370496) r3))) (let ((.def_218 (* (/ 1837054193188915 1125899906842624) r2))) (let ((.def_219 (* (- (/ 5725700885776003 9007199254740992)) r1))) (let ((.def_220 (* (/ 82389143052205 281474976710656) r0))) (let ((.def_221 (+ .def_220 .def_219 .def_218 .def_217))) (let ((.def_222 (<= .def_221 (/ 7376756447650485 9007199254740992)))) (let ((.def_223 (or .def_52 .def_222 .def_216))) (let ((.def_224 (* (/ 210175446879267 4503599627370496) r3))) (let ((.def_225 (* (/ 5328783222496893 9007199254740992) r2))) (let ((.def_226 (* (/ 5168016080979105 9007199254740992) r1))) (let ((.def_227 (* (- (/ 1908012709323115 2251799813685248)) r0))) (let ((.def_228 (+ .def_227 .def_226 .def_225 .def_224))) (let ((.def_229 (<= .def_228 (/ 1430980046204537 2251799813685248)))) (let ((.def_230 (* (- (/ 1272076611502449 2251799813685248)) r3))) (let ((.def_231 (* (/ 152088358162663 281474976710656) r2))) (let ((.def_232 (* (- (/ 239747032237133 4503599627370496)) r1))) (let ((.def_233 (* (/ 5269889006057381 9007199254740992) r0))) (let ((.def_234 (+ .def_233 .def_232 .def_231 .def_230))) (let ((.def_235 (<= .def_234 (/ 540144058408043 2251799813685248)))) (let ((.def_236 (or b1 .def_235 .def_229))) (let ((.def_237 (and .def_236 .def_223 .def_210 .def_197 .def_184 .def_171 .def_158 .def_145 .def_132 .def_119 .def_106 .def_93 .def_79 .def_66 .def_53 .def_39 .def_26 .def_13))) .def_237)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)