from .handle_FIMO import FIMOHandler
from .handle_miniF2F import miniF2FHandler
from .handle_ProofNet import ProofNetHandler
from .handle_Putnam import PutnamHandler

class HandlerManager:
    def __init__(self):
        # We store the CLASS names, not the created objects ()
        self._handler_types = {
            "FIMO": FIMOHandler,
            "miniF2F": miniF2FHandler,
            "ProofNet": ProofNetHandler,
            "Putnam": PutnamHandler
        }
        # This keeps track of what we've actually built
        self._instances = {}

    def get_handler(self, dataset_name: str):
        if dataset_name not in self._handler_types:
            raise ValueError(f"Unsupported dataset: {dataset_name}")

        # Only instantiate if we haven't used it yet
        if dataset_name not in self._instances:
            print(f"--- Initializing {dataset_name} for the first time ---")
            handler_class = self._handler_types[dataset_name]
            self._instances[dataset_name] = handler_class()
            
        return self._instances[dataset_name]