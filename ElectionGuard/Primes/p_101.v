From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two101:
  prime  472171804774597171562241157988548614480157209803071361899119875444339757982926902073922503858601070292715188186924195588242628440911761258040240385927193273145878420993373114343511978960677490275337601706059476091152459468048400267862676357229500254798476629738902029672470623683085630866367442914469451802478483079390118960903312812155286975922382799202327030284785032211889340999829897537773828398576702872481125098295626476150774248994227587524521786844242077953155341333591708705411948211311634134926339771->
  prime  2968544136617892417611810160274005139236748378031909652259766656918564058438661433338750781759024928930300388131192417663281405008012243029298991306324264108268137632785336769877659811725779381361047501925995926185075512675620292484052646257901868101918022675166485012762396392968171103024485413776089216974975380496642095457428190559315215870372105134122205231925946066850470744653996644673688763091497746043173798193405552630948350429997936884162589843901460385041843491819891283256648885658426532206822004811987.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      2968544136617892417611810160274005139236748378031909652259766656918564058438661433338750781759024928930300388131192417663281405008012243029298991306324264108268137632785336769877659811725779381361047501925995926185075512675620292484052646257901868101918022675166485012762396392968171103024485413776089216974975380496642095457428190559315215870372105134122205231925946066850470744653996644673688763091497746043173798193405552630948350429997936884162589843901460385041843491819891283256648885658426532206822004811987
      6287
      ((472171804774597171562241157988548614480157209803071361899119875444339757982926902073922503858601070292715188186924195588242628440911761258040240385927193273145878420993373114343511978960677490275337601706059476091152459468048400267862676357229500254798476629738902029672470623683085630866367442914469451802478483079390118960903312812155286975922382799202327030284785032211889340999829897537773828398576702872481125098295626476150774248994227587524521786844242077953155341333591708705411948211311634134926339771,1)::nil)
      542178248047376049428256882307339371069577145164725200208001744093738602278439619201376372687278972650801590085656344631854113466365431018893643242761219658336311829447215908549586203036104642042309338716560534746903034690108807188339885626322365591783671611293356737921822205214920343019354693311356628858204605734633275582612193174603939370434522414348995710436161383248104317350007014853591571342637494225490443151366670385259053535754711218358712562539526446466564766021222532458993853690765626332568452939519
      2288992296184820915895749291134911925420919603507050180891985261691643142612684685112158197456303201668863650503604256482940331300343159159464370471531858582347029759914032310096639812630971776242093213226199854524361036029399872932521572996169022456938175152847724318758301242154935153081874124949473262439418149252975508514130412963620072276515352835112919275335490949540866549496954782562191162027117955547440872413183951769098637607691660568811427708719889341034386442557317746680794917503943736423132599565845
      1607462676405374377970520055696159972505336810933878174274316129376179910723354505885239560098631208191270423076970476916612486208526207250787062863691638093115668131365893153191222210595551839289895529382825910545642070665799615976354581537441694449420576098843730049333809040050024322435258620507440059943977671395067247775866752593513665680554483877940296801459426271977343740088166865190999407165481457266486422479146580936931162909254676287984171445148026367689623270492913671604994064828940701270057394847114
      295900182821480571807087249118626619184327559292341362925227382047862015382373802763121588355628213948299789428800634174628131733298359224244135827422210629021892572270495170242417467290975586149176572701095681051809786396554750724642004489357922833074518959606541366248787710966989855968768456255486362242535834413416858941922650129159085480702161784152588506476460809195116731168054769735383258746867305134432197906513960010750932190622029722210963028535571887490323054420690145537800954746858293182340828869160)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.