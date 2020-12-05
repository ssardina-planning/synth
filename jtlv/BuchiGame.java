import java.io.IOException;
import java.util.Stack;
import java.util.Vector;

import net.sf.javabdd.BDD;
import net.sf.javabdd.BDD.BDDIterator;

import edu.wis.jtlv.env.Env;
import edu.wis.jtlv.env.module.SMVModule;
import edu.wis.jtlv.lib.FixPoint;


public class BuchiGame {
	
	
	
	public static void main(String[] args){
        String smvfile = args[0];
        System.out.println("SMV input module: " + smvfile);
		check(smvfile);
	}
	
	public static Vector<State> check(String smvfile){
		try {
			//Env.loadModule("./simpleagent4.smv");
            Env.loadModule(smvfile);
			SMVModule mainModule = (SMVModule) Env.getModule("main");
			//SMVModule env = (SMVModule)Env.getModule("main.env");
			//SMVModule sys = (SMVModule)Env.getModule("main.sys");
            SMVModule env = (SMVModule)Env.getModule("main.environment");
            SMVModule sys = (SMVModule)Env.getModule("main.agent");
			BDD good = mainModule.getAllDefines()[0].getBDDVal();
			BDD initial = env.initial().and(sys.initial());
            
			BDD Z = Env.TRUE();
			FixPoint<BDD> fixZ = new FixPoint<BDD>();
			while(fixZ.advance(Z)){
				BDD coxZ = env.yieldStates(sys, Z);
				BDD start = good.and(coxZ);
				BDD X = Env.FALSE();
				FixPoint<BDD> fixX = new FixPoint<BDD>();
				while(fixX.advance(X)){
					BDD coxX = env.yieldStates(sys, X);
					X = start.or(coxX);
				}
				Z=X;
			}
			
			BDD c = initial.and(Z.not());
			if(!c.isZero())
			{
				System.out.println("non realizzabile");
			}
			else
				System.out.println("realizzabile");

			Stack<BDD> stackinit = new Stack<BDD>();
			Vector<State> auto_states = new Vector<State>();
			
			BDDIterator initial_states = initial.iterator(env.moduleUnprimeVars().union(sys.moduleUnprimeVars()));

			BDD trans12 = env.trans().and(sys.trans());
			BDD trans = Z.and(trans12).and(Env.prime(Z));

			while(initial_states.hasNext())
			{
				BDD s = (BDD) initial_states.next();
				stackinit.push(s);
			}
			while(!stackinit.isEmpty())
			{
				BDD s = stackinit.pop();
				// recupera lo stato corrente oppure lo crea se non esiste
				State new_state = new State(s);
				int index = auto_states.indexOf(new_state);
				if(index == -1){
					auto_states.add(new_state);
				}else{
					new_state = auto_states.elementAt(index);
				}
				// calcola i successori dello stato corrente
				BDD succ = Env.unprime(s.and(trans).exist(Env.globalUnprimeVars()));
				BDDIterator it = succ.iterator(Env.globalUnprimeVars());
				while(it.hasNext()){
					//per ogni successore recupera lo stato successore
					// oppure se non esiste lo crea e lo aggiunge allo stack
					BDD i = (BDD) it.next();
					//					System.out.println(i.toStringWithDomains(Env.stringer));
					State succ_state = new State(i);
					int index_succ = auto_states.indexOf(succ_state);
					if(index_succ == -1)
					{
						auto_states.add(succ_state);
						stackinit.push(i);
					}else{
						succ_state = auto_states.elementAt(index_succ);
					}
					//aggiunge allo stato corrente l'indice dello stato successore
					index_succ = auto_states.indexOf(succ_state);
					new_state.add_successor_index(index_succ);
				}
			}
			String states="";
			String transs="";
			String outstring;
			//Stampa
			System.out.println("Automaton states");
			// stampa gli stati
			for(int v=0; v<auto_states.size();v++){
				String s = "State "+v+" : "+ auto_states.elementAt(v).stateToString();
				states = states+s+"\n";
			}
			int transitions = 0;
			// stampa le transizioni
			
			for(int v=0; v<auto_states.size();v++){
				State s = auto_states.elementAt(v);
				transitions = transitions+s.get_transition_number();
				transs=transs+"From "+v+" to "+ s.successorToString()+"\n";
			}
			outstring=states+transs+"Automaton has "+ auto_states.size()+ " states and " + transitions+ " transitions";
			
			System.out.println(outstring);
			return auto_states;
			
		} catch (IOException e) {
			e.printStackTrace();
			return null;
		}
	}
}
class State {
	private BDD state;
	private Vector<Integer> succ;

	public State(BDD state) {
		this.state = state;
		succ = new Vector<Integer>();
	}

	public void add_successor_index(int to_add) {
		succ.add(to_add);
	}
	
	public int get_transition_number(){
		return succ.size();
	}
	public Vector<Integer> getSuccessor(){
		return succ;
	}
	
	public boolean equals(Object other) {
		if (!(other instanceof State))
			return false;
		State other_raw = (State) other;
		return this.state.equals(other_raw.state);
	}

	public String stateToString() {
		return state.toStringWithDomains(Env.stringer);
	}
	public String successorToString(){
		String res = "";
		for(int i=0; i<succ.size();i++)
			res= res+succ.elementAt(i)+" ";
		return res;
	}
}
