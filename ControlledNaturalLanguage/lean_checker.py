from lean_interact import LeanREPLConfig, LeanServer, Command, TempRequireProject, LeanRequire
import time

t0 = time.time()
tl = t0

project = TempRequireProject(lean_version="v4.8.0", require="mathlib")
config = LeanREPLConfig(verbose=True, project = project)
server = LeanServer(config)

response = server.run(Command(cmd = "theorem ex (n : Nat) : Nat := sorry"))
print(response.messages)
print(response.messages[0].severity)
print(response.messages[0].data)

# response = server.run(Command(cmd = "def foo (n : Nat) := n + 1"))
# print(response.messages)

# response = server.run(Command(cmd = '''import Mathlib
#     def foo : Nat := "hello"'''))
# print(response.messages)
# print("Elapsed:", time.time() - tl)
# tl = time.time()

# response = server.run(Command(cmd = '''import Mathlib
#     def foo : Nat := "hello"'''))
# print(response.messages)
# print("Elapsed:", time.time() - tl)
# tl = time.time()

# response = server.run(Command(cmd = '''import Mathlib
#                               theorem add_comm_example (a b : Nat) : a + b = b + a := by 
#                               sorry'''))
# print(response.messages)
# print("Elapsed:", time.time() - tl)
# tl = time.time()



print("Total Time Spent:", time.time() - t0)

