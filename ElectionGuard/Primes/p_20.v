From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two20:
  prime  62179776254986594555174748530388657151327037739364503297378253639974582274894083220417152077801471281995983573885440788389560179597791676304337478629850662452755309626727685199496477992972749216129529730855182095229685274799986388768646146449127077510493148768030191698418474614341636998736432338061395551605844943498328180887264543995033445821818300183324992572895680432012300257065337197336795587503306051524237314945874551550556437521650066368625439853447588862336158331256278864674963927181665228503463122687291450855471563872692588886226941028149169743086195584308695051239517873519634927381257883449496321977421039018749261015309352151488197586888767898408055096800040463279211510809912046913439428885424840115319977283845372469876830471340699413674376917658549322686578264699506836530452440730016105794729880618053579396291544938008137413887929709295145152385116148126807318334930514915285504516685534907291903642866767607465305235438592594524209310288735053048252698882067835095896204648933097941791589500102411728488164935151685320954740703138590365917145567->
  prime  1124554297459028868781346810912816626373876121487437683914250526317380943933844930629419605512082553781773397649288948728396165770044505222405523333565430098846373730089788570593000946918729585116954726817853187907373815630254914423647616936310839924134434609291410067310521445438240431626590432342395592827922717939316363750399707292710472428336529818605607414164996431699916032285690734160656042906592378886234263108611236376175370927033851393163111026523973762960260590413710991135642382515785418173929188026689639982580474101613476515599974696748649933633904041199031553592199482914225567668174433228783194771262782943114536453253690839409308736442593638991653437302796075264233395242000542164247874391432129070220773850763309586336556490818568327090163422196156846731739880504610882037317000779358256455839160009575088003472680387512901156655639447273537706497845906618610266925278713114981139355123708821251590455333318445756460180912137700384696502243969165683561993283706762077476301530798333789088954175132121746153550872513429885298238350739839629800249310053654824861.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      1124554297459028868781346810912816626373876121487437683914250526317380943933844930629419605512082553781773397649288948728396165770044505222405523333565430098846373730089788570593000946918729585116954726817853187907373815630254914423647616936310839924134434609291410067310521445438240431626590432342395592827922717939316363750399707292710472428336529818605607414164996431699916032285690734160656042906592378886234263108611236376175370927033851393163111026523973762960260590413710991135642382515785418173929188026689639982580474101613476515599974696748649933633904041199031553592199482914225567668174433228783194771262782943114536453253690839409308736442593638991653437302796075264233395242000542164247874391432129070220773850763309586336556490818568327090163422196156846731739880504610882037317000779358256455839160009575088003472680387512901156655639447273537706497845906618610266925278713114981139355123708821251590455333318445756460180912137700384696502243969165683561993283706762077476301530798333789088954175132121746153550872513429885298238350739839629800249310053654824861
      18085531425
      ((62179776254986594555174748530388657151327037739364503297378253639974582274894083220417152077801471281995983573885440788389560179597791676304337478629850662452755309626727685199496477992972749216129529730855182095229685274799986388768646146449127077510493148768030191698418474614341636998736432338061395551605844943498328180887264543995033445821818300183324992572895680432012300257065337197336795587503306051524237314945874551550556437521650066368625439853447588862336158331256278864674963927181665228503463122687291450855471563872692588886226941028149169743086195584308695051239517873519634927381257883449496321977421039018749261015309352151488197586888767898408055096800040463279211510809912046913439428885424840115319977283845372469876830471340699413674376917658549322686578264699506836530452440730016105794729880618053579396291544938008137413887929709295145152385116148126807318334930514915285504516685534907291903642866767607465305235438592594524209310288735053048252698882067835095896204648933097941791589500102411728488164935151685320954740703138590365917145567,1)::nil)
      614994270479573713571050350487081361356490868504004681974274246138772211604892307430862937295051610254651490874596672230836645916155107967904091320410628038115783092624792683412090819162822142192698935827363956267329811582925579205106223399362073748615468637943571011236315733115920999542055136304137087417756615680465091276354379772137195944587326880175275968474027044906578881056279816513796769842132096374710617680516442001057271670534698298595803338320988643692216601177851876516477701885985457900525887619319613218178512909700128649108051964166942509037552788869964711957715626089214289982033159819625924265513318946253699437239235600605243210619723410888172059910343880762504079902980732524463823350913848453617966099188628863899214359043852976391160329696856036073236046439570038355867203563712018575989973255918655716278630239861732025127954391991902350840333321621001758160909905774914674464657733158500161644668310696324851562698925912448196490020109835489291845882986953290015398680511134968308182142216473647665360201640395228818473400896378328755396892639927434962
      507196120099132292963833886510783156195826722835951713946722486004743518870336920404669295730349155315916234166449258610463713201421272868113729396819163086739972101309425311432880184352621480801035056662888001076975032330978066311028356655075619265162521499790929882914458701650969116612093347560837044269547309960709803408363195569310332407550918091938863550525194137617525800449588908634226580046590533384300896471375944905984254687728878379561803331887017211356175514695497406584565296804832332849515496694614401673819601713442405186211098993395650425068301557579199375404767490810413249906809363985377555013828003906585086491951759929201273839910585486114338373741900789023384711142546039234740119465188226903376793954117353779518132966525074702987304035248233420638838488667156680915382434712064560979077633228671314648632463046057698078725902757842365380869723724562620071493507233759104204562020206750536952889712485479909413996917735447092084443656851820178831796908868352139216689371074853820259561597478124847538706255011438029261753476500861347648113488301588870912
      408970625835887232363801443204587704786481089789283188692393079048358457234267962683636693394246328398008584662944474175799394440443968085613825310687163981151663473081264713312716850277006574245695035042366829997896789023258337714184557520282535431090840348655076009312946002711685509979451573564259044605517111173626613935589852225519100206310118062637230929974109795983915858488557673941483865159853152356100109632308136745531517776289633467930427068635702666826560847384054573775468567294627556691655354204267026957137551578965764747468914413179755405527444057079756177717174216644991513711655451847503472744444790493773243074238339193079056333497661560990674741345678802083188504188595132754971929130187136556118285156805524777430530260025848992293974055245415581296294478882060355436402365101055368489070845717624926114588551538337658822197481404707221757230288609301924953330857961332861681655638639845605638711913776984455917749512034544106202459057146206457436693476492211736498046862930890618652607959551196243401394036281860435199411941728799027938109136763947216653
      329244879585291405728434522773145508113611344309245394762342788543819280225981501339579489015346495726135158837858625885419512047241484040185950255219564616021729828121704877350303116003307137415312249415219077694809436677420798045739477991567300740611386707238289781030872846666619387722794618875474539631734924669981943109137449725162063945318627704591669988402733761189467361788338246509608460151343117944326617951815878055851198152348652701303835297556995053645878971455036976005467615268630902481788888484222669784026842529773429301993716152782660584187644860983028903939379970268815923437293970631370009159188842453626104900091351022978453099494006340522678410969298547732703816309893020395326546462431665675631277971002436591958984818746685892813523682040091690532505445122079008850913974736785478970677361980576877051656929556320290096013245908102055241340777887798075624889636801572890773481904478767050830708561448114449538907409164937859318979318431715941212119418527297057837555804722869104802163219171975670040464403832863375184780723821214133927590968326739638882)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.