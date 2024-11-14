import {EventEmitter} from "events";
import {WebSocket} from "ws";

export default class DebuggerWebsocket extends EventEmitter {
	readonly #websocket: WebSocket;
	readonly #connectionPromise: Promise<void>;
	#currentMessagePromise: Promise<void>;
	#currentMessageResolver!: () => void;
	readonly #messageQueue: any[] = [];

	constructor(url: string) {
		super();
		this.#websocket = new WebSocket(url, {perMessageDeflate: false});
		this.#connectionPromise = new Promise<void>(resolve => { this.#websocket.once("open", resolve); });
		this.#currentMessagePromise = new Promise<void>(resolve => { this.#currentMessageResolver = resolve; });
		this.#websocket.on("message", rawMessage => {
			const message = JSON.parse(rawMessage.toString());
			if ("method" in message) this.emit(message.method as string, message.params as any);
			this.#messageQueue.push(message);
			if (this.#messageQueue.length === 1) {
				this.#currentMessageResolver();
				this.#currentMessagePromise = new Promise<void>(resolve => { this.#currentMessageResolver = resolve; });
			}
		});
	}

	waitForConnection(): Promise<void> {
		return this.#connectionPromise;
	}

	sendCommand(name: string, params: any = {}): void {
		this.#websocket.send(JSON.stringify({id: 1, method: name, params}));
	}

	async getMessage(): Promise<any> {
		if (this.#messageQueue.length === 0) await this.#currentMessagePromise;
		return this.#messageQueue.shift()!;
	}

	async getCommandResponse(): Promise<any> {
		while (true) {
			const message = await this.getMessage();
			if ("result" in message) return message.result;
			if ("error" in message) throw new Error(`Command failed: ${message.error.message}`);
		}
	}

	async waitForAnyEvent(): Promise<{method: string, params: any}> {
		while (true) {
			const message = await this.getMessage();
			if ("method" in message) return message;
		}
	}

	async waitForEvent(name: string): Promise<any> {
		while (true) {
			const message = await this.getMessage();
			if ("method" in message && message.method === name) return message.params;
		}
	}

	close(): void {
		this.#websocket.close();
	}
}