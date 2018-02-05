#ifndef MODELEXPORTER_HPP_
#define MODELEXPORTER_HPP_

#include <string>
#include <iostream>
#include <boost/filesystem.hpp>
#include <sqlite3.h>

class ModelExporter{
public:
	ModelExporter (std::string path_from, std::string path_to){
		p_path_from = path_from;
		p_path_to = path_to;
		p_db_from = nullptr;
		p_db_to = nullptr;
		p_db_to_use = db_transition::db_init;
		p_active_transition = active_transition::tr_init;
	}

	~ModelExporter(){

	}

	void ExportModel(){
		this->create_dir();
		this->create_db();
		this->get_free_variables();
		this->store_free_variables();
		this->get_model();
		this->store_model();
	}

	static void delete_db(){
		std::string path = "/tmp/smt/database.db";
		std::string tmp_file = "/tmp/smt/__num_of_problems__";
		boost::filesystem::remove(path);
		boost::filesystem::remove(tmp_file);
		
	}

	/**
	 * @param Callback forward function for the sqlite callback
	 *
	 * #FIXME: Make it a friend and not public!
	 */
	int __callback__(int argc, char **argv, char **azColName){
		try {
			if (p_active_transition == free_variables){
				assert (argc == 3);
				FreeVariables table_entry;
				table_entry.reg_name = argv[0];
				table_entry.resolved_name = argv[1];
				table_entry.type = argv[2];

				if(std::find(p_free_variables.begin(), p_free_variables.end(), table_entry) == p_free_variables.end()){
					p_free_variables.push_back(table_entry);
					std::cout << "inserting " << table_entry.resolved_name << std::endl;
				}
			} else if (p_active_transition == models){
				assert(argc == 3);
				Model table_entry;
				table_entry.variable = argv[0];
				table_entry.content = argv[1];
				table_entry.path = argv[2];
				p_models.push_back(table_entry);
			}
		} catch (...){
			std::cerr<< "Unknown error caught!" << std::endl;
		}
		return 0;
	}

private:
	ModelExporter (ModelExporter const & me);
	ModelExporter operator= (ModelExporter const & me);
	bool operator== (ModelExporter const & me);

	/**
	 *  @brief Used as indicator for active SQL transactions to switch between the target data structure
	 */
	enum active_transition {
		free_variables,
		tr_init,
		assertions,
		models
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
	};

  std::string p_path_from;
  std::string p_path_to;

	sqlite3 * p_db_from;
	sqlite3 * p_db_to;

	db_transition p_db_to_use;
	active_transition p_active_transition;

	std::vector<FreeVariables> p_free_variables;
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
	  	std::string tmp_file = "/tmp/smt/__num_of_problems__";
		for(auto itor = p_models.begin(); itor != p_models.end(); ++itor){
			std::stringstream query;
			query << "insert into models values ('" << itor->path <<"');";
			p_db_to_use = db_transition::target_db;
			execute_database_call(query.str());
			p_db_to_use = db_transition::target_db;
		}
		if (!boost::filesystem::exists(tmp_file)){  
		  size_t num_of_path = p_models.size();
		  std::fstream outfile;
		  outfile.open(tmp_file, std::ios::out);
		  outfile << std::to_string(num_of_path);
		  outfile.close();
		}
	}


	/**
	 * @brief Get the free variables from the forest database
	 */
	void get_free_variables (){
		std::string const query = "SELECT name, position, type FROM free_variables";
		p_active_transition = free_variables;
		p_db_to_use = db_transition::source_db;
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
			query << "insert into free_variables values ('" << itor->reg_name <<"','" << itor->resolved_name << "','" << itor->type << "');";
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
	   ModelExporter * tmp = reinterpret_cast<ModelExporter*>(data);
	   return tmp->__callback__(argc, argv, azColName);
	}
};


#endif /* MODELEXPORTER_HPP_ */
