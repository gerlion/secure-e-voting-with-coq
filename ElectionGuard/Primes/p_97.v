From Coqprime Require Import PocklingtonRefl.
Local Open Scope positive_scope.

Lemma jack_two97:
  prime  8264780458643550337606725877239838566628804727927891748430204372617483966007428097683505805868961831018911904380334568345101322461116432065977209303802264125753610584625305177791401416563819219815010706862957021518703134188024905473380270702774297978936650407488050523591435670961549817311185890697485442823691376194151988337879168368780310651351957216955389642047778124778017755214806043927242413770944143204732586671755519206662111063003194454058136010313894125807462526092444040291463739097316665609755681428460780212987548780591993209->
  prime  311516105047192699325072711764923995253372907805058095781831263212698205646751979857886700834812909334764827499903570550063559046204400557430812973078914939427905090155697002761313502193123474033267383563078576055082958533815034737102649163328968839422080227159039600335225011752766040944256483566346154516891289117018970950347674002662690587210852287507178679599133229469767328372850658635899422995821763606537515279354228953536877035561998921870800348515248360093200635976647094927766567603822257656313847882832543795562285409198432852432951.
Proof.
intro H.
apply (Pocklington_refl 
     (Ell_certif
      311516105047192699325072711764923995253372907805058095781831263212698205646751979857886700834812909334764827499903570550063559046204400557430812973078914939427905090155697002761313502193123474033267383563078576055082958533815034737102649163328968839422080227159039600335225011752766040944256483566346154516891289117018970950347674002662690587210852287507178679599133229469767328372850658635899422995821763606537515279354228953536877035561998921870800348515248360093200635976647094927766567603822257656313847882832543795562285409198432852432951
      37692
      ((8264780458643550337606725877239838566628804727927891748430204372617483966007428097683505805868961831018911904380334568345101322461116432065977209303802264125753610584625305177791401416563819219815010706862957021518703134188024905473380270702774297978936650407488050523591435670961549817311185890697485442823691376194151988337879168368780310651351957216955389642047778124778017755214806043927242413770944143204732586671755519206662111063003194454058136010313894125807462526092444040291463739097316665609755681428460780212987548780591993209,1)::nil)
      0
      78608
      17
      289)
     ((Proof_certif _ H) :: nil)).
vm_cast_no_check (refl_equal true).
Time Qed.