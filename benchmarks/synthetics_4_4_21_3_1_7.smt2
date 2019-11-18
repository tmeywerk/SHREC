(set-logic QF_LRA)
(declare-fun b3 () Bool)
(declare-fun b2 () Bool)
(declare-fun b0 () Bool)
(declare-fun b1 () Bool)
(declare-fun r0 () Real)
(declare-fun r1 () Real)
(declare-fun r2 () Real)
(declare-fun r3 () Real)
(assert (let ((.def_0 (* (- (/ 5830605205448303 2251799813685248)) r3))) (let ((.def_1 (* (/ 73198817958489 70368744177664) r2))) (let ((.def_2 (* (- (/ 4611579623638401 9007199254740992)) r1))) (let ((.def_3 (* (/ 728436078244961 1125899906842624) r0))) (let ((.def_4 (+ .def_3 .def_2 .def_1 .def_0))) (let ((.def_5 (<= .def_4 (- (/ 1182981728076623 9007199254740992))))) (let ((.def_6 (not b3))) (let ((.def_7 (not b1))) (let ((.def_8 (or .def_7 .def_6 .def_5))) (let ((.def_9 (* (- (/ 2829271088705011 9007199254740992)) r3))) (let ((.def_10 (* (- (/ 7521505099954849 9007199254740992)) r2))) (let ((.def_11 (* (/ 1824227952491649 4503599627370496) r1))) (let ((.def_12 (* (- (/ 83247356542005 1125899906842624)) r0))) (let ((.def_13 (+ .def_12 .def_11 .def_10 .def_9))) (let ((.def_14 (<= .def_13 (- (/ 330922965699731 2251799813685248))))) (let ((.def_15 (not b0))) (let ((.def_16 (or .def_15 .def_7 .def_14))) (let ((.def_17 (* (- (/ 609999174646751 562949953421312)) r3))) (let ((.def_18 (* (- (/ 4034219654846145 4503599627370496)) r2))) (let ((.def_19 (* (/ 100385559761535 562949953421312) r1))) (let ((.def_20 (* (- (/ 4334679396020749 9007199254740992)) r0))) (let ((.def_21 (+ .def_20 .def_19 .def_18 .def_17))) (let ((.def_22 (<= .def_21 (- (/ 7293304843851237 9007199254740992))))) (let ((.def_23 (or .def_6 b2 .def_22))) (let ((.def_24 (* (- (/ 14051671812217 70368744177664)) r3))) (let ((.def_25 (* (/ 409179464626897 9007199254740992) r2))) (let ((.def_26 (* (/ 1904301601693753 2251799813685248) r1))) (let ((.def_27 (* (- (/ 2477349780181695 4503599627370496)) r0))) (let ((.def_28 (+ .def_27 .def_26 .def_25 .def_24))) (let ((.def_29 (<= .def_28 (/ 945599134608387 2251799813685248)))) (let ((.def_30 (or b2 b3 .def_29))) (let ((.def_31 (* (/ 3034771436842219 4503599627370496) r3))) (let ((.def_32 (* (- (/ 4960683947852365 9007199254740992)) r2))) (let ((.def_33 (* (- (/ 420963539551391 1125899906842624)) r1))) (let ((.def_34 (* (- (/ 6476508206968341 9007199254740992)) r0))) (let ((.def_35 (+ .def_34 .def_33 .def_32 .def_31))) (let ((.def_36 (<= .def_35 (- (/ 544123589445651 4503599627370496))))) (let ((.def_37 (or b0 b3 .def_36))) (let ((.def_38 (* (/ 531591076280955 9007199254740992) r3))) (let ((.def_39 (* (- (/ 1603769777696707 1125899906842624)) r2))) (let ((.def_40 (* (- (/ 2676080197848543 9007199254740992)) r1))) (let ((.def_41 (* (- (/ 4051349265664459 2251799813685248)) r0))) (let ((.def_42 (+ .def_41 .def_40 .def_39 .def_38))) (let ((.def_43 (<= .def_42 (- (/ 3631648685867607 4503599627370496))))) (let ((.def_44 (or b3 b1 .def_43))) (let ((.def_45 (* (- (/ 5120083672827979 4503599627370496)) r3))) (let ((.def_46 (* (- (/ 1757042729919141 4503599627370496)) r2))) (let ((.def_47 (* (/ 2983666658904729 9007199254740992) r1))) (let ((.def_48 (* (/ 910461021765219 4503599627370496) r0))) (let ((.def_49 (+ .def_48 .def_47 .def_46 .def_45))) (let ((.def_50 (<= .def_49 (- (/ 162618123065835 1125899906842624))))) (let ((.def_51 (not b2))) (let ((.def_52 (or .def_51 .def_15 .def_50))) (let ((.def_53 (* (/ 68872963135137 2251799813685248) r3))) (let ((.def_54 (* (- (/ 427694535039233 4503599627370496)) r2))) (let ((.def_55 (* (/ 7488359011445657 4503599627370496) r1))) (let ((.def_56 (* (/ 2187344998056931 4503599627370496) r0))) (let ((.def_57 (+ .def_56 .def_55 .def_54 .def_53))) (let ((.def_58 (<= .def_57 (/ 3853731793729253 2251799813685248)))) (let ((.def_59 (or .def_6 .def_7 .def_58))) (let ((.def_60 (* (- (/ 1759992851279441 2251799813685248)) r3))) (let ((.def_61 (* (- (/ 5840212238036479 9007199254740992)) r2))) (let ((.def_62 (* (/ 5764818394965899 9007199254740992) r1))) (let ((.def_63 (* (- (/ 1009207651173115 9007199254740992)) r0))) (let ((.def_64 (+ .def_63 .def_62 .def_61 .def_60))) (let ((.def_65 (<= .def_64 (- (/ 62962542564227 2251799813685248))))) (let ((.def_66 (or .def_6 b1 .def_65))) (let ((.def_67 (* (- (/ 2465820376291535 4503599627370496)) r3))) (let ((.def_68 (* (/ 3514280942928161 4503599627370496) r2))) (let ((.def_69 (* (- (/ 596448004976611 2251799813685248)) r1))) (let ((.def_70 (* (/ 167744738104317 2251799813685248) r0))) (let ((.def_71 (+ .def_70 .def_69 .def_68 .def_67))) (let ((.def_72 (<= .def_71 (/ 1642569020842163 4503599627370496)))) (let ((.def_73 (or b2 .def_7 .def_72))) (let ((.def_74 (* (- (/ 422619329718471 1125899906842624)) r3))) (let ((.def_75 (* (/ 743816167795739 2251799813685248) r2))) (let ((.def_76 (* (/ 1780492583627501 9007199254740992) r1))) (let ((.def_77 (* (- (/ 3239905680196809 2251799813685248)) r0))) (let ((.def_78 (+ .def_77 .def_76 .def_75 .def_74))) (let ((.def_79 (<= .def_78 (- (/ 496582071438345 4503599627370496))))) (let ((.def_80 (or .def_51 .def_7 .def_79))) (let ((.def_81 (* (/ 166413056015617 2251799813685248) r3))) (let ((.def_82 (* (/ 406972242013165 2251799813685248) r2))) (let ((.def_83 (* (/ 2437502467041535 9007199254740992) r1))) (let ((.def_84 (* (/ 6206546113830241 9007199254740992) r0))) (let ((.def_85 (+ .def_84 .def_83 .def_82 .def_81))) (let ((.def_86 (<= .def_85 (/ 3999736060073443 4503599627370496)))) (let ((.def_87 (or .def_51 b3 .def_86))) (let ((.def_88 (* (- (/ 2966797626792537 9007199254740992)) r3))) (let ((.def_89 (* (/ 1025012075585723 1125899906842624) r2))) (let ((.def_90 (* (- (/ 3470274255125253 2251799813685248)) r1))) (let ((.def_91 (* (/ 7984802885465911 9007199254740992) r0))) (let ((.def_92 (+ .def_91 .def_90 .def_89 .def_88))) (let ((.def_93 (<= .def_92 (/ 3466615297253211 4503599627370496)))) (let ((.def_94 (or .def_7 .def_15 .def_93))) (let ((.def_95 (* (/ 6075029113781357 9007199254740992) r3))) (let ((.def_96 (* (/ 1997109586068849 4503599627370496) r2))) (let ((.def_97 (* (- (/ 840462272609965 4503599627370496)) r1))) (let ((.def_98 (* (- (/ 420840165979191 562949953421312)) r0))) (let ((.def_99 (+ .def_98 .def_97 .def_96 .def_95))) (let ((.def_100 (<= .def_99 (/ 281855555918337 562949953421312)))) (let ((.def_101 (or b3 .def_7 .def_100))) (let ((.def_102 (* (/ 2157526597118553 9007199254740992) r3))) (let ((.def_103 (* (/ 4156848888031817 2251799813685248) r2))) (let ((.def_104 (* (- (/ 2167597442705349 2251799813685248)) r1))) (let ((.def_105 (* (- (/ 207330415691257 9007199254740992)) r0))) (let ((.def_106 (+ .def_105 .def_104 .def_103 .def_102))) (let ((.def_107 (<= .def_106 (/ 2878357143630035 2251799813685248)))) (let ((.def_108 (or b3 b1 .def_107))) (let ((.def_109 (* (- (/ 3712522481710495 4503599627370496)) r3))) (let ((.def_110 (* (/ 1186980801724905 4503599627370496) r2))) (let ((.def_111 (* (/ 4644717861354827 4503599627370496) r1))) (let ((.def_112 (* (/ 6962914482612703 9007199254740992) r0))) (let ((.def_113 (+ .def_112 .def_111 .def_110 .def_109))) (let ((.def_114 (<= .def_113 (/ 4438976390270861 4503599627370496)))) (let ((.def_115 (or b1 .def_15 .def_114))) (let ((.def_116 (* (- (/ 2277579810965207 4503599627370496)) r3))) (let ((.def_117 (* (- (/ 135599629427067 281474976710656)) r2))) (let ((.def_118 (* (- (/ 3460058717738129 9007199254740992)) r1))) (let ((.def_119 (* (- (/ 3907357856402769 2251799813685248)) r0))) (let ((.def_120 (+ .def_119 .def_118 .def_117 .def_116))) (let ((.def_121 (<= .def_120 (- (/ 1865546097288585 2251799813685248))))) (let ((.def_122 (or .def_6 .def_7 .def_121))) (let ((.def_123 (* (- (/ 3669704973087739 4503599627370496)) r3))) (let ((.def_124 (* (/ 315840028690583 2251799813685248) r2))) (let ((.def_125 (* (/ 1661644942209415 9007199254740992) r1))) (let ((.def_126 (* (/ 2907442727028729 9007199254740992) r0))) (let ((.def_127 (+ .def_126 .def_125 .def_124 .def_123))) (let ((.def_128 (<= .def_127 (/ 591935922871235 2251799813685248)))) (let ((.def_129 (or b1 .def_6 .def_128))) (let ((.def_130 (* (- (/ 2847012154203675 4503599627370496)) r3))) (let ((.def_131 (* (/ 3114893477050551 4503599627370496) r2))) (let ((.def_132 (* (/ 7342223351386883 9007199254740992) r1))) (let ((.def_133 (* (- (/ 455221219440615 1125899906842624)) r0))) (let ((.def_134 (+ .def_133 .def_132 .def_131 .def_130))) (let ((.def_135 (<= .def_134 (/ 6276550480342231 9007199254740992)))) (let ((.def_136 (or .def_51 b1 .def_135))) (let ((.def_137 (* (- (/ 990899468943091 4503599627370496)) r3))) (let ((.def_138 (* (/ 2434228481741575 1125899906842624) r2))) (let ((.def_139 (* (- (/ 71357162349865 281474976710656)) r1))) (let ((.def_140 (* (- (/ 4702656109465867 9007199254740992)) r0))) (let ((.def_141 (+ .def_140 .def_139 .def_138 .def_137))) (let ((.def_142 (<= .def_141 (/ 2939204251831169 2251799813685248)))) (let ((.def_143 (or .def_15 .def_6 .def_142))) (let ((.def_144 (* (- (/ 2069533535452961 2251799813685248)) r3))) (let ((.def_145 (* (/ 2731041354107027 4503599627370496) r2))) (let ((.def_146 (* (/ 391604478460041 1125899906842624) r1))) (let ((.def_147 (* (- (/ 6583817172498833 4503599627370496)) r0))) (let ((.def_148 (+ .def_147 .def_146 .def_145 .def_144))) (let ((.def_149 (<= .def_148 (/ 23378469251505 4503599627370496)))) (let ((.def_150 (or b1 .def_15 .def_149))) (let ((.def_151 (and .def_150 .def_143 .def_136 .def_129 .def_122 .def_115 .def_108 .def_101 .def_94 .def_87 .def_80 .def_73 .def_66 .def_59 .def_52 .def_44 .def_37 .def_30 .def_23 .def_16 .def_8))) .def_151)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
(check-sat)
