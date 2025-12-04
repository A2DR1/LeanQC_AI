from CNL_generation import generate_cnl_list, read_cnl_lst, write_cnl_to_file
from FL_generation import generate_write

CNL_path = 'history/CNL'
Lean_files_path = 'history/Lean_files'
NL_FL_pairs_path = 'history/NL_FL_pairs'
folder_path = "miniF2F/informal/test"

if __name__ == "__main__":
    version = input("Version: ")

    cnl_statements = generate_cnl_list(folder_path, limit=100, version=version)
    write_cnl_to_file(cnl_statements, filename=f"{CNL_path}/cnl_statements_v{version}.json")

    generate_write(f"{CNL_path}/cnl_statements_v{version}.json", name=f"{Lean_files_path}/Autoformalized_CNL_v{version}.lean", json_output_path=f"{NL_FL_pairs_path}/NL_FL_pairs_CNL_v{version}.json")

    print(f"\n✅ Saved CNL statements to {CNL_path}/cnl_statements_v{version}.json")
    print(f"\n✅ Saved CNL autoformalizations to {Lean_files_path}/Autoformalized_CNL_v{version}.lean")
    print(f"\n✅ Saved NL-FL pairs to {NL_FL_pairs_path}/NL_FL_pairs_CNL_v{version}.json")