#ifndef LEARNMODEL_HPP_
#define LEARNMODEL_HPP_

#include <string>
#include <iostream>
#include <boost/filesystem.hpp>
#include <sqlite3.h>

#define DEBUG

class LearnModel{
public:
	LearnModel (std::string path_from, std::string path_to){
		p_path_from = path_from;
		p_path_to = path_to;
		p_db_from = nullptr;
		p_db_to = nullptr;
		p_db_to_use = db_transition::db_init;
		p_active_transition = active_transition::tr_init;
	}

	~LearnModel(){

	}

  void learn_use_case (){
		this->create_dir();
		this->create_db();
		this->get_free_variables(db_transition::source_db);
		this->extract_select_variables();
		this->get_model();
		this->check_model();
		this->store_free_variables();
		this->store_model();
	}

  void verify_learned_model() {
	this->create_db();
	this->get_free_variables(db_transition::target_db);
	this->extract_select_variables();
	this->get_learned_model();
	this->check_learned_model();
  }

	static void delete_db(){
		std::string path = "/tmp/smt/database.db";
		boost::filesystem::remove(path);
	}

	/**
	 * @param Callback forward function for the sqlite callback
	 *
	 * #FIXME: Make it a friend and not public!
	 */
	int __callback__(int argc, char **argv, char **azColName){
		try {
		  if (p_active_transition == active_transition::free_variables){
				assert (argc == 3);
				FreeVariables table_entry;
				table_entry.reg_name = argv[0];
				table_entry.resolved_name = argv[1];
				table_entry.type = argv[2];

				if(std::find(p_free_variables.begin(), p_free_variables.end(), table_entry) == p_free_variables.end()){
					p_free_variables.push_back(table_entry);
#ifdef DEBUG
					std::cout << "inserting " << table_entry.resolved_name << std::endl;
#endif
				}
		  } else if (p_active_transition == active_transition::models){
			assert(argc == 3);
			Model table_entry;
			table_entry.variable = argv[0];
			table_entry.content = argv[1];
			table_entry.path = argv[2];
			p_models.push_back(table_entry);
		  } else if (p_active_transition == active_transition::learned_models){
			p_learned_models.push_back(argv[0]);
		  }
		} catch (...){
		  std::cerr<< "Unknown error caught!" << std::endl;
		}
		return 0;
	}

private:
	LearnModel (LearnModel const & me);
	LearnModel operator= (LearnModel const & me);
	bool operator== (LearnModel const & me);

	/**
	 *  @brief Used as indicator for active SQL transactions to switch between the target data structure
	 */
	enum active_transition {
		free_variables,
		tr_init,
		assertions,
		models,
		learned_models
	};

	enum db_transition {
		source_db,
		target_db,
		db_init
	};

	/**
	 * @brief Represent a database entry for a free variable
	 */
	struct FreeVariables {
		std::string reg_name;
		std::string resolved_name;
		std::string type;

		bool operator== (FreeVariables const & fv){
			return  !resolved_name.compare(fv.resolved_name);
		}
	};

	struct Model{
	  std::string variable;
	  std::string content;
	  std::string path;
	  int sat_path;
	};

  std::string p_path_from;
  std::string p_path_to;

	sqlite3 * p_db_from;
	sqlite3 * p_db_to;

	db_transition p_db_to_use;
	active_transition p_active_transition;

  std::vector<FreeVariables> p_free_variables;
  std::vector<FreeVariables> p_select_variables;
  std::vector<std::string> p_learned_models;
  std::vector<Model> p_models;
	/**
	 * @brief Check if target folder exists, create if not
	 */
	void create_dir(){
		try{
			if(!boost::filesystem::exists(p_path_to)){
				boost::filesystem::create_directories(p_path_to);
			}
		} catch (std::exception const & ex){
			std::cerr << ex.what() << std::endl;
		}
	}

	/*
	 * @brief Creates or opens the target db, opens the source db
	 */
	void create_db(){
		try {
			std::string source_db = p_path_from + "database.db";
			if (sqlite3_open_v2(source_db.c_str(), &p_db_from, SQLITE_OPEN_READWRITE, nullptr ) != SQLITE_OK){
				throw std::runtime_error("Can not open source database!");
			}

			std::string target_db = p_path_to + "database.db";
			if(boost::filesystem::exists(target_db)){
				if (sqlite3_open_v2(target_db.c_str(), &p_db_to, SQLITE_OPEN_READWRITE, nullptr ) != SQLITE_OK){
					throw std::runtime_error("Can not open target database!");
				}
			} else {
				if (sqlite3_open_v2(target_db.c_str(), &p_db_to, SQLITE_OPEN_CREATE | SQLITE_OPEN_READWRITE, nullptr ) != SQLITE_OK){
					throw std::runtime_error("Can not create target database!");
				}

				std::stringstream free_variables_table;
				free_variables_table << "create table free_variables(";
				free_variables_table << "name varchar(5000),";
				free_variables_table << "position varchar(5000),";
				free_variables_table << "type varchar(5000)";
				free_variables_table << ");";
				p_db_to_use = db_transition::target_db;
				this->execute_database_call(free_variables_table.str());
				p_db_to_use = db_transition::db_init;

				std::stringstream learn_models_table;
				learn_models_table << "create table learned_models(";
				learn_models_table << "smt varchar(5000),";
				learn_models_table << "path integer";
				learn_models_table << ");";
				p_db_to_use = db_transition::target_db;
				this->execute_database_call(learn_models_table.str());
				p_db_to_use = db_transition::db_init;

				std::stringstream models_table;
				models_table << "create table models(";
				models_table << "smt varchar(5000)";
				models_table << ");";
				p_db_to_use = db_transition::target_db;
				this->execute_database_call(models_table.str());
				p_db_to_use = db_transition::db_init;
				
				std::stringstream allsat_table;
				allsat_table << "create table allsat(";
				allsat_table << "name varchar(5000),";
				allsat_table << "value varchar(50),";
				allsat_table << "solution integer,";
				allsat_table  << "path varchar(5000)";
				allsat_table << ");";
				p_db_to_use = db_transition::target_db;
				this->execute_database_call(allsat_table.str());
				p_db_to_use = db_transition::db_init;
			}
		} catch (std::exception const & ex){
			std::cerr << ex.what() << std::endl;
		}
	}


	void get_model(){
		std::string const query = "SELECT variable, content, path FROM models";
		p_active_transition = models;
		p_db_to_use = db_transition::source_db;
		execute_database_call(query);
		p_active_transition = tr_init;
		p_db_to_use = db_transition::db_init;
	}

  
	void store_model(){
	  for(auto itor = p_models.begin(); itor != p_models.end(); ++itor){
		std::vector<std::string> single_assertions = split(itor->path, ",");
		for(auto inner_itor = single_assertions.begin(); inner_itor != single_assertions.end(); ++inner_itor){
		  std::stringstream query;
		  query << "INSERT INTO learned_models values ('" << *inner_itor <<"'," << itor->sat_path << ");";
		  p_db_to_use = db_transition::target_db;
		  execute_database_call(query.str());
		  p_db_to_use = db_transition::target_db;
		}
	  }
	  std::stringstream query;
	  query << "INSERT INTO learned_models (smt) values ('end_use_case');";
	  p_db_to_use = db_transition::target_db;
	  execute_database_call(query.str());
	  p_db_to_use = db_transition::target_db;
	}


	/**
	 * @brief Get the free variables from the forest database
	 */
	void get_free_variables (db_transition source){
		std::string const query = "SELECT name, position, type FROM free_variables";
		p_active_transition = free_variables;
		p_db_to_use = source;
		execute_database_call(query);
		p_db_to_use = db_transition::db_init;
		p_active_transition = tr_init;
	}

	/*
	 * @brief Store free variables to the permanent database
	 */
	void store_free_variables (){
		for(auto itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
			std::stringstream query;
			query << "INSERT INTO free_variables (name, position, type) ";
			query << "SELECT '" << itor->reg_name <<"','" << itor->resolved_name << "','" << itor->type << "' " ;
			query << "WHERE NOT EXISTS (SELECT position FROM free_variables WHERE position='" << itor->resolved_name << "');";
			p_db_to_use = db_transition::target_db;
			execute_database_call(query.str());
			p_db_to_use = db_transition::target_db;
		}

		for(auto itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
		  std::stringstream query;
		  query << "INSERT INTO free_variables (name, position, type) ";
		  query << "SELECT '" << itor->reg_name <<"','" << itor->resolved_name << "','" << itor->type << "' " ;
		  query << "WHERE NOT EXISTS (SELECT position FROM free_variables WHERE position='" << itor->resolved_name << "');";
		  p_db_to_use = db_transition::target_db;
		  execute_database_call(query.str());
		  p_db_to_use = db_transition::target_db;
		}
	}


	/**
	 * @brief Dummy function for database transactions
	 *
	 * @param query The SQL query to execute as std::string
	 */
	void execute_database_call (std::string query) {
#ifdef DEBUG
		std::cout << "Executing Database Query: " << query << std::endl;
#endif
		try {
			sqlite3 * current_db;
			if (p_db_to_use == db_transition::target_db){
				current_db = p_db_to;
			} else {
				current_db = p_db_from;
			}

			if(sqlite3_exec(current_db, query.c_str(), c_callback, this, NULL) != 0){
				std::string msg = "Can not execute the following QUERY:\n" + query;
				throw std::runtime_error(msg);
			}
		} catch (std::runtime_error & err){
			std::cerr<< err.what() << std::endl;
		}
	}

	/**
	 * @brief Static callback function for the sqlite3 api
	 * This static function gets the this pointer of the class and forwards the
	 * data to an actual member of the class to have access to the memory
	 */
	static int c_callback(void *data, int argc, char **argv, char **azColName){
	   LearnModel * tmp = reinterpret_cast<LearnModel*>(data);
	   return tmp->__callback__(argc, argv, azColName);
	}

  /*
   * @brief Only export models which represent the SAT path for an error free model
   */
  void check_model(){
	std::string tmp_file = "/tmp/smt/check_model.smt2";
	std::vector<Model> next_models;
	
	int sat_path = 0;
	for(auto itor = p_models.begin(); itor != p_models.end(); ++itor){
	  this->export_smt2(*itor, tmp_file);
	  bool sat = this->execute_model(tmp_file);
	  boost::filesystem::remove(tmp_file);
	  if (!sat){
		std::cout << "unsat" << std::endl;
	  } else {
		std::cout << "sat" << std::endl;
		Model tmp;
		tmp.path = itor->path;
		tmp.sat_path = sat_path;
		tmp.variable = itor->variable;
		tmp.content = itor->content;
		next_models.push_back(tmp);
	  }
	  sat_path++;
	}

	p_models.clear();
	std::copy(next_models.begin(), next_models.end(), std::back_inserter(p_models));
  }

  void check_learned_model(){
	std::string tmp_path = "/tmp/smt/learned_model.smt2";
	std::stringstream stream;
	this->write_header(stream);
	this->write_variables(stream);
	for(auto itor = p_learned_models.begin(); itor != p_learned_models.end(); ++itor){
	  Model m;
	  m.path = *itor;
	  this->write_clauses(stream, m);
	}
	this->write_end(stream);
	
	std::fstream out_file(tmp_path, std::ios::out);
	out_file << stream.str();
	out_file.close();

	bool sat = this->execute_model(tmp_path);
	//boost::filesystem::remove(tmp_path);
	std::string res = sat == true ? "sat" : "unsat";
	std::cout << "Learned Model is: " << res << std::endl;
   
  }

  /*
   * @brief Export a model to an smt2 file
   *
   * @param m The model to export
   * @param path The path where to export the model to
   */
  void export_smt2(Model const & m, std::string const & path){
	std::stringstream stream;
	this->write_header(stream);
	this->write_variables(stream);
	this->write_clauses(stream,m);
	this->write_end(stream);

	std::fstream out_file(path, std::ios::out);
	out_file << stream.str();
	std::cout << stream.str() << std::endl;
	out_file.close();
  }

  
  /*
   * @brief Execute the smt2 file at path
   *
   * @param path Path to the smt2 file
   * @return True iff the instance is SAT, else false
   */
  bool  execute_model(std::string const & path){
	std::string z3 = "z3";
	
	boost::process::ipstream is; //reading pipe-stream
	boost::process::child c(boost::process::search_path("z3"), path, boost::process::std_out > is);
	
	std::vector<std::string> result;
	std::string line;
	
	while (c.running() && std::getline(is, line) && !line.empty()){
	  result.push_back(line);
	  std::cout << line << std::endl;
	}

	return is_sat(result.front());
  }

  /*
   * @brief Evaluate if an execute smt2 instance is sat using Z3 output
   *
   * @param line The first line of the Z3 output containing the result
   * @return True if SAT, else false
   */
  bool is_sat(std::string const & line){
	if (line.find("unsat") != std::string::npos){
	  return false;
	} else if (line.find("sat") != std::string::npos){
	  return true;
	} else {
	  return false;
	}
  }

  
  /*
   * @brief Write a generic smt2 header
   *
   * @param stream The stringstream to write the header to
   */
  void write_header (std::stringstream & stream){
	std::string header_options = "(set-option :produce-models true)";
	stream << header_options << std::endl;
  }


  /*
   * @brief Write all free variables to the smt2 file
   *
   * @param stream The stringstream to write to
   */
  void write_variables(std::stringstream & stream){
	for(auto itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
	  std::string name = itor->resolved_name;
	  std::string type = itor->type;
	  std::string resolved_type = this->resolve_type(type);
	  stream << "(declare-fun " <<  name  << " ()  " << resolved_type << ")" << std::endl;
	}
	for(auto itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
	  std::string name = itor->resolved_name;
	  std::string type = itor->type;
	  std::string resolved_type = this->resolve_type(type);
	  stream << "(declare-fun " <<  name  << " ()  " << resolved_type << ")" << std::endl;
	}	
  }


  /*
   * @brief Write assertions to the smt2 file
   *
   * @param stream The stringstream to write to
   * @param m The model for which we want to dump the assertions
   */
  void write_clauses(std::stringstream & stream, Model const & m){
	std::string remove_comma = m.path.substr(0, m.path.size()-1);
	std::vector<std::string> assertions = split(remove_comma, ",");
	
	for(auto itor = assertions.begin(); itor != assertions.end(); ++itor){
	  	stream << "(assert " << *itor << ")" << std::endl;
	}

	
	for(auto itor = p_select_variables.begin(); itor != p_select_variables.end(); ++itor){
	  stream << "(assert ( not " << itor->resolved_name << " ))" << std::endl;
	}	
  }

  
  /*
   * @brief Write the ending part of an smt2 instance
   *
   * @param stream The stringstream to write to
   */
  void write_end(std::stringstream & stream){
	stream << "(check-sat)" << std::endl;
	stream << "(get-model)" << std::endl;
  }

  
  /**
   * @brief Transform a LLVM Datatype to a SMT2 Datatype
   * @param type The type to transform
   * @return The transformed value
   */
  std::string resolve_type(std::string const & type){
	try {
	  if (type == "IntegerTyID32"){
		return "(_ BitVec 32)";
	  } else if (type == "IntegerTyID1"){
		return "Bool";
	  } else {
		throw new std::runtime_error("Datatype not supported yet!");
	  }
	} catch (std::exception const & ex){
	  std::cerr << ex.what() << std::endl;
	}
  }

  
  /**
   * @brief Extract the select variables out of the free variables
   */
  void extract_select_variables(){
#ifdef DEBUG
	std::cout << "Extract Select Variables..." << std::endl;
#endif
	std::string select = "select_enable";
	std::vector<FreeVariables> next_free_variables;
	std::vector<FreeVariables>::iterator itor;
	for(itor = p_free_variables.begin(); itor != p_free_variables.end(); ++itor){
	  if(itor->resolved_name.find(select) != std::string::npos){
		FreeVariables tmp;
		tmp.resolved_name = itor->resolved_name;
		tmp.reg_name = itor->reg_name;
		tmp.type = itor->type;
		p_select_variables.push_back(tmp);
	  } else {
		next_free_variables.push_back(*itor);
	  }
	}
	
	p_free_variables.clear();
	std::copy(next_free_variables.begin(),next_free_variables.end(), std::back_inserter(p_free_variables));	
  }

  void get_learned_model(){
#ifdef DEBUG
	std::cout << "Get learned Model" << std::endl;
#endif
	std::string const query = "SELECT smt, path FROM learned_models";
	p_active_transition = active_transition::learned_models;
	p_db_to_use = db_transition::target_db;
	execute_database_call(query);
	p_active_transition = active_transition::tr_init;
	p_db_to_use = db_transition::db_init;
  }

  
  /**
   * @brief Split a string at delimiter and pack them into a vector
   *
   * @param str The string to split
   * @param delim The delimiter to use
   */
  std::vector<std::string> split(std::string const & str, std::string const & delim) {
	std::vector<std::string> tokens;
	size_t prev = 0;
	size_t pos = 0;

	do
	  {
		pos = str.find(delim, prev);
		if (pos == std::string::npos) pos = str.length();
		std::string token = str.substr(prev, pos-prev);
		if (!token.empty()) tokens.push_back(token);
		prev = pos + delim.length();
	  }
	while (pos < str.length() && prev < str.length());

	return tokens;
  }
};

#endif /* LEARNMODEL_HPP_ */
