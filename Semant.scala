class Semant(var program : Program, var options : CoolOptions)
extends CoolVisitor()
{
  var io : IO = new IO();
  var errors : SemantErrors = new SemantErrors(options);
  var class_table : ClassTable = null;

  def run() : Boolean = {
    program.accept(this);
    !errors.has_errors()
  };

  var any_sym : Symbol = io.symbol("Any");

  // #(
  def consym(s : String, sym : Symbol) : String =
    s.concat(sym.toString().concat("'"));

  var nothing_sym : Symbol = io.symbol("Nothing");
  var symbol_sym : Symbol = io.symbol("Symbol");
  var native_sym : Symbol = io.symbol("native");
  var null_sym : Symbol = io.symbol("Null");

  var any_class_info : ClassInfo = null;
  var root_methods : MethodTable = new MethodTable();
  var root_environment : Environment = null;
  var feature_tables_ready : Boolean = false;
  // #)

  override def visit_program(the_node:Cprogram,classes:Classes) : Any = {
    class_table = new ClassTable(classes,errors);
    root_environment = new RootEnvironment(class_table,errors);
    // XXX: Check for illegal redeclared classes?
  
    var enum : Enumeration = classes.elements();
    while (enum.hasNext()) {
      var child_node : Cclass_decl = null;
      enum.next() match { 
        case x:Cclass_decl => child_node = x
      };

      if (!(child_node.get_name() == any_sym)) {
        var child_info : ClassInfo = class_table.lookup(child_node.get_name());
        var parent_info : ClassInfo = class_table.lookup(child_node.get_parent());
        var parent_node : Cclass_decl = parent_info.get_class_decl();
        
        // Assign child_info reference to parent_info
        child_info.set_parent_info(parent_info);


        // Check that parent class is inheritable
        if (is_null(parent_node)) ()
        else if (!parent_node.get_inheritablep()) {
          err(parent_node,consym("cannot inherit from class ",child_node.get_parent()));
          child_info.setWellFormed(false)
        } else {
          parent_info.add_subclass(child_node.get_name());
          child_node.set_superclass(parent_node)
        }
      } else child_node.set_superclass(null)
    };

    // Check for cycles
    checkCycles(classes);

    // Check for Main
    var query : Cclass_decl = class_table.lookup_class(symbol("Main"));
    if (is_null(query)) {
      err(the_node,"Main not found")
    } else ();  // XXX: Check Main for args?

    

    // Populate method and attr tables for all classes
    new FeatureInstaller(classes,class_table,errors);
    feature_tables_ready = true;

    var emu : ClassesEnumeration = classes.elements();
    while (emu.hasNext()) {
      var foo : ClassInfo = class_table.get_info(emu.next());
      if (!foo.isWellFormed()) {
        foo.set_parent_info(null)
      } else ()
    };

    classes.accept(this);
    // In PA4 - you need to set program attributes
    //#(
    // In PA5 - you need to arrange checks for circular inheritance etc,
    //          check for Main
    the_node.set_any_class(class_table.lookup_class(any_sym));
    the_node.set_int_class(class_table.lookup_class(int_sym));
    the_node.set_unit_class(class_table.lookup_class(unit_sym));
    the_node.set_boolean_class(class_table.lookup_class(bool_sym));
    the_node.set_string_class(class_table.lookup_class(string_sym));
    //#)

    ()
  };

  def checkCycles(classes : Classes) : Any = {
    var visited: Hashtable = new Hashtable();
    var class_enum: Enumeration = classes.elements();
    while (class_enum.hasNext()) {
      class_enum.next() match {
        case x:Cclass_decl => visited.put(x.get_name(),false)
      }
    };

    // Recursive
    explore(any_sym,visited);

    class_enum = visited.elements();
    while (class_enum.hasNext()) {
      class_enum.next() match {
        case p:Pair => 
          var lost_sym : Symbol = null;
          p.first() match {
            case s:Symbol => lost_sym = s
          };
          p.second() match {
            case b:Boolean => if (!b) {
              err(class_table.lookup_class(lost_sym),consym("cyclic inheritance found at class ",lost_sym));
              class_table.lookup(lost_sym).setWellFormed(false)
            } else ()
          }
      }
    }
  };

  def explore(root : Symbol,visit : Hashtable) : Any = {
    visit.get(root) match {
      case b:Boolean => 
        if (b) {
          err(class_table.lookup_class(root),consym("cyclic inheritance found at class ",root));
          class_table.lookup(root).setWellFormed(false)
        } else {
          visit.put(root,true);
          var children : Enumeration = class_table.lookup(root).subclass_elements();
          while (children.hasNext()) {
            children.next() match {
              case s:Symbol => explore(s,visit)
            }
          }
        }
    }
  };

  override def visit_Classes_one(node:Class) : Any = node.accept(this);
  override def visit_class_decl(cd:Cclass_decl,name:Symbol,parent:Symbol,
                                features:Features,filename:Symbol) : Any = {
    // for PA4, check that name is not illegal
    // #(
    if (name == nothing_sym)
      errors.error(cd,cd,"Cannot declare class Nothing")
    else if (name == null_sym) 
           errors.error(cd,cd,"Cannot declare class Null")
         else ();
    // #)
    // for PA5, check superclass, inheritance (##)
    {
      current_class = cd;
      current_info = class_table.lookup(name);
      current_env = new ClassEnvironment(current_class,current_info,root_environment);
      // TODO PA4/PA5: set current_env
      features.accept(this)
    } 
  };
  
  var current_class : Cclass_decl = null;
  var current_info : ClassInfo = null;
  var current_env : Environment = null;

  def err(loc : CoolNode, message : String) : Unit =
    errors.error(current_class,loc,message);

  override def visit_Features_one(f : Feature) : Any = {
    //##PA5: TODO: set "owner" attribute
    f.set_owner(current_class);
    f.accept(this)
  };

  override def visit_attr(the_node:Cattr,name:Symbol,of_type:Symbol) : Any = {
    // #(
    var of_class : Cclass_decl = class_table.lookup_class(of_type);
    if (of_type == nothing_sym) 
      err(the_node,"attributes may not be given type Nothing")
    else if (of_type == null_sym) ()
    else if (is_null(of_class)) 
      err(the_node,consym("class of attribute undeclared: ",of_type))
    else the_node.set_feature_of_class(of_class)
    // #)
    // PA4: TODO: check types, set attributes
  };

  override def visit_method(m:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,body:Expression) : Unit = {
    // #(
    table_env = new TableEnvironment(current_env);
    formals.accept(this);
    check_expr(body,table_env);
    var of_class : Cclass_decl = class_table.lookup_class(return_type);
    m.set_feature_of_class(of_class);
    if (is_null(of_class)) 
      if (return_type == nothing_sym) ()
      else if (return_type == null_sym) ()
      else err(m,consym("return type undeclared: ",return_type))
    else {};
    // PA5: TODO check that overridden method (if any) is correctly overridden
    // #)
    // PA4: TODO: set up the current environment (with formals), check types
    //      check that body type checks, 
    
    // XXX: Check for duplicate methods?
    var inher_method : Cmethod = current_info.lookup_method(name);
    if (!class_table.get_info(current_class).isWellFormed()) ()
    else if (overridep) {
      m.set_overrides(inher_method);
      // Check that inher_method != null
      if (!is_null(inher_method)) {
        // TODO Check for equivelence in formals:
        //    - # of args
        //    - types of args
        //    -return type
        if (formals.size() == inher_method.get_formals().size()) {
          var enum_child : FormalsEnumeration = formals.elements();
          var enum_parent : FormalsEnumeration = inher_method.get_formals().elements();
          var blo : Boolean = enum_child.hasNext();
          while (blo) {
            var fc : Cformal = enum_child.next() match { case x:Cformal => x };
            var fp : Cformal = enum_parent.next() match { case x:Cformal => x };
            if (is_null(fc.get_formal_of_class())) ()
            else if (is_null(fp.get_formal_of_class())) ()
            else if (fc.get_of_type() == fp.get_of_type()) ()
            else { err(m,"overriden method contains mismatch formal type"); blo = false };
            if (blo) blo = enum_child.hasNext() else ()
          }
        } else err(m,consym("overriden method has wrong number of formals: ",name));
        var inher_ret : Symbol = inher_method.get_return_type();
        table_env.check_type_leq(m,"return type of overriding method",return_type,inher_ret)
      } else err(m,"method has no matching method to override")
    } else {
      if (!is_null(inher_method)) err(m,consym("method missing override keyword ",name))
      else ()
    }
  };

  // #(

  var table_env : TableEnvironment = null;

  override def visit_Formals_one(f : Formal) : Any = f.accept(this);

  override def visit_formal(f:Cformal,name:Symbol,of_type:Symbol) : Any = {
    if (!is_null(table_env.probe(name))) 
      err(f,consym("redeclared formal ",name))
    else table_env.add(name,f);
    var of_class : Cclass_decl = class_table.lookup_class(of_type);
    if (of_type == nothing_sym) null
    else if (of_type == null_sym) null
    else if (is_null(of_class)) 
      err(f,consym("undeclared class: ",of_type))
    else f.set_formal_of_class(of_class)
  };

  var unit_sym : Symbol = io.symbol("Unit");
  var bool_sym : Symbol = io.symbol("Boolean");
  var int_sym : Symbol = io.symbol("Int");
  var string_sym : Symbol = io.symbol("String");
  var ignore_sym : Symbol = io.symbol("_ignore");
  var error_type : Symbol = nothing_sym;

  def check_expr(e : Expression, env : Environment) : Symbol = {
    // println("Checking " + e);
    e.set_of_type(e match {
      case n:Cno_expr => nothing_sym
	
      case v:Cvariable =>
	var vb : CoolNode = env.lookup(v.get_name());
  e.set_binding(vb);
  if (is_null(vb)) { 
	  err(v,consym("undeclared variable: ",v.get_name())); 
	  error_type 
	} else binding_type(vb)

      case a:Cassign =>
	var vtype : Symbol = any_sym;
        var name : Symbol = a.get_name();
        var b : CoolNode = env.lookup(a.get_name());
        if (is_null(b)) b = a.get_binding() else a.set_binding(b);
	b match {
	  case null =>
	    err(a,consym("undeclared variable in assignment ",name))
	  case b:Case =>
	    err(a,consym("cannot assign to branch variable ",name))
	  case t:Class =>
	    err(a,"cannot assign to 'this'")
	  case f:Formal =>
	    err(a,consym("cannot assign to formal ",name))
	  case vb:CoolNode =>
	    vtype = binding_type(vb)
	};
        env.check_type_leq(a,consym("assignment to ",name),
			   check_expr(a.get_expr(),env),vtype);
        unit_sym

      case d:Cdispatch =>
        check_exprs(d.get_actuals(),env);
	check_expr(d.get_expr(),env) match {
	  case null => nothing_sym
	  case s:Symbol => 
	    check_dispatch(d,s,d.get_name(),d.get_actuals())
	}

      case d:Cstatic_dispatch =>
        check_exprs(d.get_actuals(),env);
        if (is_null(class_table.lookup_class(d.get_type_name())))
          err(d,consym("Undeclared class: ",d.get_type_name())) // redundant
	else
        // The following check should never fail
          env.check_type_leq(d,"internal static dispatch",
		  	     check_expr(d.get_expr(),env),d.get_type_name());
        check_dispatch(d,d.get_type_name(),d.get_name(),d.get_actuals())

      case c:Ccond =>
	check_bool(c,"predicate of 'if'",c.get_pred(),env);
        env.type_lub(check_expr(c.get_then_exp(),env),
		     check_expr(c.get_else_exp(),env))

      case l:Cloop =>
	check_bool(l,"predicate of 'while'",l.get_pred(),env);
        check_expr(l.get_body(),env);
        unit_sym

      case c:Ctypecase =>
	check_expr(c.get_expr(),env);
        var vt : Symbol = c.get_expr().get_of_type();
        var cs : Cases = c.get_cases();
        var rt : Symbol = nothing_sym;
        var ei : CasesEnumeration = cs.elements();
        while (ei.hasNext()) {
	  ei.next() match {
	    case ci:Cbranch =>
	      var is : Symbol = ci.get_local_type();
	      if (is == null_sym) 
		if (symbol_name(ci.get_name()) == "null")
		  if (current_env.type_leq(is,vt)) ()
		  else err(ci, consym("Case not possible for ",vt).concat(": 'Null'"))
	        else err(ci,"'Null' cannot be explicitly checked for, use 'null'")
	      else if (is == nothing_sym) err(ci,"'Nothing' is not a legal case")
	      else class_table.lookup_class(is) match {
		case null => err(ci,consym("Undeclared case class: ",is))
		case cd:Cclass_decl => ci.set_case_of_class(cd);
		  if (current_env.type_leq(is,vt)) () else
		    if (current_env.type_leq(vt,is)) () else
		      err(ci,consym(consym("Case not possible for ",vt).concat(": "), is))
	      };
	      var done : Boolean = false;
              var ej : CasesEnumeration = cs.elements();
	      while (!done) {
                ej.next() match {
		  case cj:Cbranch =>
		    if (ci == cj) done = true
		    else if (if (is == null_sym) cj.get_local_type() == null_sym
			     else current_env.type_leq(is,cj.get_local_type()))
		      { err(ci,consym("Case already covered: ",is));
		        done = true }
		    else ()
		}
	      };
	      var newenv : Environment =
		new SingleEnvironment(ci.get_name(),ci,env);
	      var ty : Symbol = check_expr(ci.get_expr(),newenv);
	      ci.set_case_of_type(ty);
	      rt = env.type_lub(rt,ty)
	  }
	};
        rt

      case b:Cblock => 
	check_exprs(b.get_body(),env)

      case l:Clet =>
	var n : Symbol = l.get_identifier();
        var ty : Symbol = l.get_local_type();
        if (!is_null(env.lookup(n)))
	  err(l,consym("local shadows existing variable ",n))
	else null;
	class_table.lookup_class(ty) match {
	  case null =>
	    if (ty == null_sym) ()
	    else if (ty == nothing_sym) ()
	    else err(l,consym("type of local is undeclared: ",ty))
	  case cd:Cclass_decl => 
	    l.set_of_class(cd)
	};
        env.check_type_leq(l,consym("initialization of ",n),
			   check_expr(l.get_init(),env),ty);
        check_expr(l.get_body(),new SingleEnvironment(n,l,env))

      case op:Cadd =>
	check_binary(op,"+",op.get_e1(),op.get_e2(),env); int_sym

      case op:Csub =>
	check_binary(op,"-",op.get_e1(),op.get_e2(),env); int_sym

      case op:Cmul =>
	check_binary(op,"*",op.get_e1(),op.get_e2(),env); int_sym

      case op:Cdiv =>
	check_binary(op,"/",op.get_e1(),op.get_e2(),env); int_sym

      case op:Cneg =>
	check_int(op,"operand of '-'",op.get_e1(),env); int_sym

      case op:Clt =>
	check_binary(op,"<",op.get_e1(),op.get_e2(),env); bool_sym

      case op:Cleq =>
	check_binary(op,"<=",op.get_e1(),op.get_e2(),env); bool_sym

      case op:Ccomp =>
	check_bool(op,"operand of '!'",op.get_e1(),env); bool_sym

      case l:Cint_lit => int_sym
      case l:Cbool_lit => bool_sym
      case l:Cstring_lit => string_sym

      case a:Calloc =>
	var t : Symbol = a.get_type_name();
        if (t == bool_sym) err(a,"cannot instantiate value class Boolean")
        else if (t == int_sym) err(a,"cannot instantiate value class Int")
        else if (t == unit_sym) err(a,"cannot instantiate value class Unit")
        else if (t == any_sym) err(a,"cannot instantiate value class Any")
        else if (t == symbol_sym) err(a,"cannot instantiate value class Symbol")
	else class_table.lookup_class(t) match {
	  case null => 
	    err(a,consym("undeclared class for 'new': ",t))
	  case cd:Cclass_decl =>
	    a.set_of_class(cd)
	};
        t

      case u:Cunit => unit_sym
      case u:Cnil => null_sym
    });
    e.get_of_type()
  };

  var last_type : Symbol = null;
  def check_exprs(es : Expressions, env : Environment) : Symbol = {
    var saved : Environment = current_env;
    current_env = env;
    last_type = unit_sym;
    es.accept(this);
    current_env = saved;
    last_type
  };
  override def visit_Expressions_one(e : Expression) : Any =
    last_type = check_expr(e,current_env);
  
  def check_binary(op : CoolNode, name : String, e1 : Expression, e2 : Expression, env: Environment) : Unit = {
    check_int(op,"left operand of '".concat(name).concat("'"),e1,env);
    check_int(op,"right operand of '".concat(name).concat("'"),e2,env)
  };

  def check_int(n : CoolNode, desc : String, e:Expression, env:Environment) : Unit =
    if (! (check_expr(e,env) == int_sym))
      err(n,desc.concat(" must be 'Int'"))
    else ();

  def check_bool(n : CoolNode, desc : String, e:Expression, env:Environment) : Unit =
    if (!(check_expr(e,env) == bool_sym))
      err(n,desc.concat(" must be 'Boolean'"))
    else ();

  def binding_type(c : CoolNode) : Symbol =
    c match {
      case null => null
      case cd:Cclass_decl => cd.get_name()
      case a:Cattr => a.get_of_type()
      case f:Cformal => f.get_of_type()
      case l:Clet => l.get_local_type()
      case b:Cbranch => b.get_local_type()
    };

  def check_dispatch(e:Expression,tn:Symbol,mn:Symbol,es:Expressions) : Symbol={
    var info : ClassInfo = class_table.lookup(tn);
    var bound : Cmethod = info.probe_method(mn);
    if (is_null(bound)) bound = info.lookup_method(mn) else ();
    e.set_mbinding(bound);
    var m : Cmethod = e.get_mbinding();
    if (!is_null(m)) {
      var fs : Formals = m.get_formals();
      var n : Int = fs.size();
      if (!(es.size() == n))
	err(e,"Wrong number of parameters (".concat(es.size().toString())
	    .concat(") to ").concat(mn.toString()).concat("', expected ")
	    .concat(n.toString()))
      else {
	var fe : FormalsEnumeration = fs.elements();
        var ee : ExpressionsEnumeration = es.elements();
	var i : Int = 0;
	while (fe.hasNext()) {
          i = i + 1;
	  fe.next() match {
	    case f:Cformal =>
	      current_env.check_type_leq(e,"parameter #".concat(i.toString()),
					 ee.next().get_of_type(),f.get_of_type())
	  }
	}
      };
      m.get_return_type()
    } else error_type
  };
  //#)
}


class SemantErrors(var options : CoolOptions) extends IO()
{
  var num_errors : Int = 0;

  def error(cd : Cclass_decl, loc : CoolNode, s: String) : Unit = 
  {
    if (options.get_semant_debug())
      out_any(loc)
    else {
      if (is_null(cd)) out("<unknown>") 
      else out(symbol_name(cd.get_filename()));
      out(":").out_any(loc.get_line_number())
    };
    out(": ").out(s).out("\n");
    num_errors = num_errors + 1
  };

  def has_errors() : Boolean = 0 < num_errors;
}


/**
 * This class represents a partially implemented interface
 * used with the DECORATOR
 * design pattern.  Please read up on this design pattern.
 */
class Environment() extends IO()
{
  def err(loc : CoolNode, message : String) : Unit = abort("abstract!");

  def error(cd : Cclass_decl, loc : CoolNode, message : String) : Unit =
    abort("abstract!");

  def lookup(key : Symbol) : CoolNode = abort("abstract");

  def type_leq(t1 : Symbol, t2 : Symbol) : Boolean = type_lub(t1,t2) == t2;

  def check_type_leq(n : CoolNode, s : String, t1 : Symbol, t2 : Symbol):Unit =
    if (!type_leq(t1,t2)) 
      err(n,"Type mismatch at ".concat(s)) 
    else ();

  def type_lub(t1 : Symbol, t2 : Symbol) : Symbol = abort("abstract!");
}

// #(
class RootEnvironment(var class_table : ClassTable, var errors : SemantErrors) 
extends Environment()
{
  override def lookup(key : Symbol) : CoolNode = null;
  override def error(cd : Cclass_decl, loc : CoolNode, message : String):Unit =
    errors.error(cd,loc,message);
  override def err(loc : CoolNode, message : String) : Unit =
    error(null,loc,message);

  var any_sym : Symbol = symbol("Any");
  var null_sym : Symbol = symbol("Null");
  var nothing_sym : Symbol = symbol("Nothing");
  var bool_sym : Symbol = symbol("Boolean");
  var int_sym : Symbol = symbol("Int");
  var unit_sym : Symbol = symbol("Unit");

  override def type_lub(t1 : Symbol, t2 : Symbol) : Symbol = {
    if (t1 == t2) t1
    else if (t1 == nothing_sym) t2
    else if (t2 == nothing_sym) t1
    else if (t1 == bool_sym) any_sym
    else if (t2 == bool_sym) any_sym
    else if (t1 == int_sym) any_sym
    else if (t2 == int_sym) any_sym
    else if (t1 == unit_sym) any_sym
    else if (t2 == unit_sym) any_sym
    else if (t1 == null_sym) t2
    else if (t2 == null_sym) t1
    else {
      var s1 : SymbolStack = new SymbolStack();
      var s2 : SymbolStack = new SymbolStack();
      var info_1 : ClassInfo = class_table.lookup(t1);
      if (is_null(info_1.get_class_decl())) info_1 = null else ();
      var info_2 : ClassInfo = class_table.lookup(t2);
      if (is_null(info_2.get_class_decl())) info_2 = null else ();
      while (!is_null(info_1)) {
        if (!is_null(info_1.get_class_decl())) {
          s1.push(info_1.get_class_decl().get_name());
          info_1 = info_1.get_parent_info()
        } else  info_1 = null
      };
      while (!is_null(info_2)) {
        if (!is_null(info_2.get_class_decl())) {
          s2.push(info_2.get_class_decl().get_name());
          info_2 = info_2.get_parent_info()
        } else info_2 = null
      };
      var rType : Symbol = nothing_sym;
      var cond : Boolean = true;
      if (s1.isEmpty()) cond = false
      else if (s2.isEmpty()) cond = false
      else cond = s1.peek() == s2.peek();
      while (cond) {
        rType = s1.pop(); 
        s2.pop();
        if (s1.isEmpty()) cond = false
        else if (s2.isEmpty()) cond = false
        else cond = s1.peek() == s2.peek()
      };
      rType
    }
  };
}
// #)

/**
 * A abstract Decorator (q.v.) for a nested contour.
 * This class is extended by concrete decorator classes.
 * Compare to java.io.FilterOutputStream.
 */ 
class NestedEnvironment(var outer : Environment) extends Environment() 
{
  override def error(cd : Cclass_decl, loc : CoolNode, message : String):Unit =
    outer.error(cd,loc,message);

  override def err(loc : CoolNode, message : String) : Unit =
    outer.err(loc,message);

  override def lookup(key : Symbol) : CoolNode = outer.lookup(key);

  override def type_lub(t1 : Symbol, t2 : Symbol) : Symbol = 
    outer.type_lub(t1,t2);
}

// #(
class TableEnvironment (var outere : Environment) 
extends NestedEnvironment(outere)
{
  var table : Hashtable = new Hashtable();

  def probe(key : Symbol) : CoolNode = {
    table.get(key) match {
      case null => null
      case vb:CoolNode => vb
    }
  };

  override def lookup(key : Symbol) : CoolNode = {
    table.get(key) match {
      case null => super.lookup(key)
      case vb:CoolNode => vb
    }
  };

  def add(name : Symbol, vb : CoolNode) : Unit = {
    table.put(name,vb); ()
  };
}
// #)

/**
 * A concrete decorator for a contour with a single declaration.
 */
class SingleEnvironment (var name : Symbol, var node : CoolNode, var outere : Environment) 
extends NestedEnvironment(outere)
{
  override def lookup(key : Symbol) : CoolNode =
    if (key == name) node else super.lookup(key);
}

// #(
class ClassEnvironment(var class_decl : Cclass_decl, var info : ClassInfo,
		       var superenv : Environment) 
extends TableEnvironment(superenv)
{
  { add(symbol("this"),class_decl) };

  override def err(loc : CoolNode, message : String) : Unit =
    superenv.error(class_decl,loc,message);

  override def lookup(key : Symbol) : CoolNode = {
    var r : CoolNode = super.lookup(key);
    if (is_null(r)) {
      info.probe_attr(key) match {
        case null => info.lookup_attr(key)
        case node:CoolNode => node
      }
    } else r
  };
}
// #)
// PA4: Define new environment classes
//      The solution has three other environment classes.
//      Only two are used in the PA4 solution.

class ClassTable(var classes : Classes, var errors : SemantErrors) 
extends CoolVisitor() 
{
  var table : Hashtable = new Hashtable();

  { classes.accept(this) } ;

  override def visit_Classes_one(cl : Class) : Any = cl.accept(this);
  // #(
  override def visit_class_decl(n : Cclass_decl, name:Symbol,parent:Symbol,
		       features:Features,filename:Symbol) : Any =
    if (is_null(table.get(name)))
      table.put(name,new ClassDeclInfo(n,errors))
    else null;
  // #)
  // Use Visitor to insert every class into the table.
  // For PA4, the value can be the class_decl node itself
  // For PA5, you may want to put in a structure that
  //          can be used as a node in the inheritance graph.

  // #(
  var no_info : ClassInfo = new ClassInfo();

  def lookup(sym : Symbol) : ClassInfo = {
    if (is_null(sym)) no_info
    else table.get(sym) match {
      case null => no_info
      case ci:ClassInfo => ci
    }
  };

  def lookup_class(sym : Symbol) : Cclass_decl = lookup(sym).get_class_decl();

  def get_info(c:Class) : ClassInfo = {
    c match {
      case null => no_info
      case cd:Cclass_decl => lookup(cd.get_name())
    }
  };
  /* #)
  def lookup_class(sym : Symbol) : Cclass_decl = abort("TODO");
  ## */
}

// #(
class ClassInfo() extends IO()
{
  def get_class_decl() : Cclass_decl = null;
  def get_parent_info() : ClassInfo = null;
  def set_parent_info(ci : ClassInfo) : Any = null;
  def add_subclass(c : Symbol) : Any = null;
  def subclass_elements() : Enumeration = null;
  def add_method(m : Symbol,n : Cmethod) : Any = null;
  def probe_method(m : Symbol) : Cmethod = null;
  def lookup_method(m : Symbol) : Cmethod = null;
  def add_attr(a : Symbol,n : Cattr) : Any = null;
  def probe_attr(a : Symbol) : Cattr = null;
  def lookup_attr(a : Symbol) : Cattr = null;
  def isWellFormed() : Boolean = false;
  def setWellFormed(b : Boolean) : Any = null;
  // Add other "abstract" methods here.
}

class ClassDeclInfo(var class_decl : Cclass_decl, var errors : SemantErrors) 
extends ClassInfo() {
  var parent_info : ClassInfo = null;
  var subclass_list : Vector = new Vector();
  var method_table : MethodTable = new MethodTable();
  var attr_table : AttrTable = new AttrTable();
  var wellFormed : Boolean = true;
  override def get_class_decl() : Cclass_decl = class_decl;
  override def get_parent_info() : ClassInfo = parent_info;
  override def set_parent_info(ci : ClassInfo) : Any = parent_info = ci;
  override def add_subclass(c : Symbol) : Any = subclass_list.add(c);
  override def subclass_elements() : Enumeration = subclass_list.elements();
  override def add_method(m : Symbol,n : Cmethod) : Any = method_table.put(m,n);
  override def probe_method(m : Symbol) : Cmethod = method_table.lookup(m);
  override def lookup_method(m : Symbol) : Cmethod = {
    if (is_null(parent_info)) null
    else if (!wellFormed) null
    else {
      parent_info.probe_method(m) match {
        case null => parent_info.lookup_method(m)
        case c:Cmethod => c
      }
    }
  };
  override def add_attr(a : Symbol,n : Cattr) : Any = attr_table.put(a,n);
  override def probe_attr(a : Symbol) : Cattr = attr_table.lookup(a);
  override def lookup_attr(a : Symbol) : Cattr = {
    if (is_null(parent_info)) null
    else if (!wellFormed) null
    else {
      parent_info.probe_attr(a) match {
        case null => parent_info.lookup_attr(a)
        case c:Cattr => c
      }
    }
  };
  override def isWellFormed() : Boolean = wellFormed;
  override def setWellFormed(b : Boolean) : Any = wellFormed = b;
}

class MethodTable() {
  var table : Hashtable = new Hashtable();
  def lookup(m : Symbol) : Cmethod = {
    table.get(m) match { 
      case null => null
      case c:Cmethod => c 
    }
  };
  def put(m : Symbol,n : Cmethod) : Any = table.put(m,n);
}

class AttrTable() {
  var table : Hashtable = new Hashtable();
  def lookup(a : Symbol) : Cattr = {
    table.get(a) match { 
      case null => null
      case c:Cattr => c 
    }
  };
  def put(a : Symbol,n : Cattr) : Any = table.put(a,n);
}

class FeatureInstaller(var classes : Classes, var ct : ClassTable, var errors : SemantErrors) 
extends CoolVisitor()
{
  { classes.accept(this) };

  override def visit_Classes_one(cl : Class) : Any = cl.accept(this);
  override def visit_class_decl(n:Cclass_decl,name:Symbol,parent:Symbol,features:Features,filename:Symbol) : Any = {
    current_info = ct.lookup(name);
    features.accept(this)
  };

  var current_info : ClassInfo = null;

  override def visit_Features_one(f : Feature) : Any = f.accept(this);
  override def visit_attr(node:Cattr,name:Symbol,of_type:Symbol) : Any = {
    current_info.add_attr(name,node)
  };
  override def visit_method(m:Cmethod,overridep:Boolean,name:Symbol,formals:Formals,return_type:Symbol,body:Expression) : Unit = {
    current_info.add_method(name,m);
    ()
  };
}

class Vector() {
  var size : Int = 0;
  var arr : ArrayAny = new ArrayAny(size);

  def get_size() : Int = size;
  
  def add(elem : Any) : Unit = {
    if (arr.length() == size) {
      arr = arr.resize((arr.length() + 1) * 2)
    } else { };
    arr.set(size, elem);
    size = size + 1
  };

  def elements() : Enumeration = new VectorEnumeration(arr, size);

  def clear() : Boolean = {
    size = 0;
    arr.resize(size);
    true
  };
}
  
class VectorEnumeration(var v : ArrayAny, var s : Int) extends Enumeration() {
  var index : Int = -1;
  var vec : ArrayAny = v;
  var size : Int = s;

  override def hasNext() : Boolean = !index.equals(size-1);

  override def next() : Any = {
    if (hasNext()) {
      index = index + 1;
      vec.get(index)
    } else abort("No Such Element.")  
  };
}

class SymbolStack() extends IO() {
  var top : SymbolNode = null;
  var size : Int = 0;

  def isEmpty() : Boolean = size == 0;

  def push(s : Symbol) : Any = {
    top = new SymbolNode(s,top); 
    size = size + 1
  };

  def pop() : Symbol = {
    if (isEmpty()) abort("No such element.") else ();
    var sym : Symbol = top.getSym();
    top = top.getNext();
    size = size - 1;
    sym
  };

  def peek() : Symbol = if (isEmpty()) abort("No such element.") else top.getSym();
}

class SymbolNode(var elem : Symbol,var next : SymbolNode) {
  def getSym() : Symbol = elem;
  def getNext() : SymbolNode = next;
}

