import {WebSocket} from "ws";

export type TaskInfo = {
	projectId: string,
	taskId: string,
	taskKind: string
};

export default class StatusStore {
	#currentTask: TaskInfo | null = null;
	#progressMessage: string = "";

	#listeners: WebSocket[] = [];

	putTask(taskInfo: TaskInfo): void {
		if (this.#currentTask !== null) throw new Error("A task is already running.");
		this.#currentTask = taskInfo;
		this.#progressMessage = "Starting...";
	}

	updateTaskProgress(progressMessage: string): void {
		console.log(progressMessage);
		this.#progressMessage = progressMessage;
		for (const listener of this.#listeners)
			listener.send(JSON.stringify({status: "taskRunning", message: progressMessage}));
	}

	finishTask(success: boolean = true): void {
		for (const listener of this.#listeners) {
			listener.send(JSON.stringify({status: "taskDone", success}));
			listener.close();
		}
		this.#listeners = [];
		this.#currentTask = null;
		console.log("Task done.");
	}

	get hasRunningTask(): boolean {
		return this.#currentTask !== null;
	}

	get currentTask(): TaskInfo | null {
		return this.#currentTask;
	}

	onSocketConnection(socket: WebSocket): void {
		socket.on("message", message => {
			let projectId = "", taskId = "";
			try {
				const data = JSON.parse(message.toString());
				if (
					!("projectId" in data) || typeof data["projectId"] !== "string"
					|| !("taskId" in data) || typeof data["taskId"] !== "string"
				) throw new Error();
				({projectId, taskId} = data as {projectId: string, taskId: string});
			} catch {
				socket.send(JSON.stringify({status: "invalid"}));
				return;
			}
			if (
				this.#currentTask === null
				|| projectId !== this.#currentTask.projectId || taskId !== this.#currentTask.taskId
			) {
				socket.send(JSON.stringify({status: "noTask"}));
				socket.close();
				return;
			}
			socket.send(JSON.stringify({status: "taskRunning", message: this.#progressMessage}));
			this.#listeners.push(socket);
		});
	}
}