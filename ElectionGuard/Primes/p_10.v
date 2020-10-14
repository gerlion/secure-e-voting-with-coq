From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two10:
  prime  44901785981483928269468656314582515361597607665230930023370555137452201643885990359870055423564237657423907522745279487260536535193636145228170958180973473369095484938405780110133173828743281740518691807317084554025313261637418794164880738620723122782127497526720557351677904376390613353232387121631321340949532692010726114566017091085486453988246954742343390714170476957862286780305602248376940576027972939135210987427313971181017303254233911634970819172183956019228536891122564973916661040395458007680111846965552633528962145172457250160958233229656515821470170356393858520767431923785902556203918837299550932151635840013880391615402130395487651247053682181727158789142501585119520350651816722514643180860913479490191049589426502602584872351233533148408438532559788424399837053033824505704786203565764253933089711709777802467112391514265006060770051627779603875749871417848778435936071098696358328187256486838919184029843805215671194877774902185021501924909613318565319242154132516923859984363382308663711899925560450606529044861251538356116238423268495478847304405667346633576687422940369443889449129332948012347188850483394137858961851087133->
  prime  44303155370778784537780100188596501266796788359838071264298978896359688891569702336392267844657279240975131987652039421136379062106434588139988982966504735022138703933206954249704878355258476308354096608141933182751047785233268726801074548613431642109196173729694318881065334555244573696007092936525732564831993522160839114006622951227134748583675646341718468629169156159060066772950567959201579204268368003910660354542933021317231980567248465125053388210980399517580182037290118937684404115404905761521720595821807885818754021853018050101812338064238735152538330045202415599389256265235312749176567022895136213761943212814660751339856952859037304883878773831527333486081604420053515914127650169712080038666593736931550798162191814248984953998250477305234242326809416531723439827129524391023431074986829420531693752280325151537239458782265144071946171503653424751898865084559903384037991466575394980756309302214982283274477416980573069456512288489231075106771153402016867178681602297500125166330829377943877055595507075523266372419484335193316060281653756571088803808475254477817508104067782732599521431904625944602866536010893680177543417386120087779.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      44303155370778784537780100188596501266796788359838071264298978896359688891569702336392267844657279240975131987652039421136379062106434588139988982966504735022138703933206954249704878355258476308354096608141933182751047785233268726801074548613431642109196173729694318881065334555244573696007092936525732564831993522160839114006622951227134748583675646341718468629169156159060066772950567959201579204268368003910660354542933021317231980567248465125053388210980399517580182037290118937684404115404905761521720595821807885818754021853018050101812338064238735152538330045202415599389256265235312749176567022895136213761943212814660751339856952859037304883878773831527333486081604420053515914127650169712080038666593736931550798162191814248984953998250477305234242326809416531723439827129524391023431074986829420531693752280325151537239458782265144071946171503653424751898865084559903384037991466575394980756309302214982283274477416980573069456512288489231075106771153402016867178681602297500125166330829377943877055595507075523266372419484335193316060281653756571088803808475254477817508104067782732599521431904625944602866536010893680177543417386120087779
      986668
      ((44901785981483928269468656314582515361597607665230930023370555137452201643885990359870055423564237657423907522745279487260536535193636145228170958180973473369095484938405780110133173828743281740518691807317084554025313261637418794164880738620723122782127497526720557351677904376390613353232387121631321340949532692010726114566017091085486453988246954742343390714170476957862286780305602248376940576027972939135210987427313971181017303254233911634970819172183956019228536891122564973916661040395458007680111846965552633528962145172457250160958233229656515821470170356393858520767431923785902556203918837299550932151635840013880391615402130395487651247053682181727158789142501585119520350651816722514643180860913479490191049589426502602584872351233533148408438532559788424399837053033824505704786203565764253933089711709777802467112391514265006060770051627779603875749871417848778435936071098696358328187256486838919184029843805215671194877774902185021501924909613318565319242154132516923859984363382308663711899925560450606529044861251538356116238423268495478847304405667346633576687422940369443889449129332948012347188850483394137858961851087133,1)::nil)
      38096821858551383034674318723998077492778427203088152117788586058307502466965294903129384668935744873556501124764480733070373532870527061686675689771688444162878169722778400155342864758736594902870951433272425916769473830784854398760928959546171977123234603117427864166635794798586407700840263194676979667751259221924833817150299635259369518446897844750965566461416261625084865606855977249397675929682779594953281092116048279603447177355027193924469430036843226487279654994816394188393107293663218537646755971564415780203391680293891409368896229358218748866776730979426672389681365987523279398680325012263691741191692800064244937466166705007669676610356050735014316434288764896870545641184336990479210470138182170497361645259358221177375453111816520274767838493432569733619058763963205070830086337289361103044266990260147249828045312961485425616019795407919218505579551792406596340502251919025522766007471396300467366514502799501048926580649122890980071696543880998148158299251064269489803303496406525207214585558351900190675164124106264919278537100633388170353097034754595420968954506144586494336787986560006924280009454416109957460489866605425167082
      482384207345706283753930572509002566178378863259003162830874433307418426393047978403775729858028536393177608326491034436877522149884317634211263338304212822528977495553524897934457894567425188497825661063353398032527812203077470042100575420890351825011096621422855687329610656997627513105497535848133188938113756688994350329031462155730987967904651144278555115618335323326831393764606086543264799641840504460516978800129395088376187860008506185505810557792556746246436032961949030458791784254037761104492018515917894644952625406988427716069427211932048538120170875365211671944370102288776960682951760347824455877902220108713723028932461972791888074868083016279154926088512723052058217499526241915270552116126643358427318106319253334385259839986203297791470181681520875019051811062461152419698468929006930886149687675317914218379834010886478418934386030264709028784395507808495995598756336184094028908708234917970950433134525667220304741782651886150821968990239970338659802893179916024490331970764240812440601396311781527567527461782737148013844679798751841674717137867839671304972663031648273817930248482023283529081823422700139209140794004026444110
      12381752419545895456142824374666243603843908300792902287435151428051927089738692841574854282243772492538100724344878620793315307491097916292892619357398221360806425846901522716955821184179940787193413045845402093237236346609662777340004456356797319216990261034881045359453744240429421750032569338739701032110360141403987579658700732168899370404130005112388248859733625086641369817866936691694875605927129805907590780492638420990630573742390601363846327278393653942634077106894706334298923916095041191158247829340778773618923573124598730118487522620816675203138936382716361360255805216491099376158886310862090947125105697338310539638722671419966516602776826378827615940000334952613745701098068815482992958997217069841357785222868840088387030556172056563490070010964459260926633053592647938302814686756408744756922443024521528846950886612964086706491454256629863868859128532287810134146624357588356595936779203077735509583813546982406759267711091918319939117624166980723467821486812334082490625938593019838723589984577460044582770459877393065315658828586401724458597112049744241737530375249673271186699056092206373199183613509364467463957511085027601629
      9355613984090434012070270055292719486331387253877244336815510774788666858024520669603805650860476552936078029192882666096049553034692893249912668077479598348007814378320092897189732594998730402424481044410602824660604205405727456980824379687883983079724517596296813333592612594186657542971274140304346404089341569549996493778408514752859828516528111380512621396792447070390759440087564426052873564602683033425918304991858973269129899874755729252820193886171267449803532128454250769831422948438621702120694056409705807823321821890243262943478196748602977549043278592462555676421383381622089403310572538441162063412903081177261384707219108941595706668978885318659339632617548742020921804932745543751145587833958370504755109127353171918159171591649992948608817418550212431156697205404315311945930230439798408380676181359110541590103741481125174340310275142236968105976543190890589079884111151081946945895816171875584003442604538934328573020242384255196245659653322742997277253005674899261485325229246380339053894209982563876242501042520872875757947982549074971277897921402492337262273113225220295996775720355757581113998048626331897587544694349672419969)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.