local RunService = game:GetService("RunService")

local ThreadController = {}
ThreadController.__index = ThreadController

local LoopController = {}
LoopController.__index = LoopController
LoopController.Thread = ThreadController

function LoopController.new()
	local self = setmetatable({
		Threads = {},
		ThreadCount = 0,
	}, LoopController)

	self.Connection = RunService.Heartbeat:Connect(function(deltaTime)
		local threads = self.Threads
		for i = self.ThreadCount, 1, -1 do
			local thread = threads[i]
			if thread then
				thread:handle(deltaTime)
			end
		end
	end)

	return self
end

function LoopController:newThread(rate, func, repeatTimes)
	local thread = ThreadController.new(rate, func, repeatTimes)
	local count = self.ThreadCount + 1
	self.ThreadCount = count
	self.Threads[count] = thread
	thread._index = count
	thread._owner = self
	return thread
end

function LoopController:removeThread(thread)
	local idx = thread._index
	if not idx then
		return
	end
	local threads = self.Threads
	local count = self.ThreadCount
	threads[idx] = threads[count]
	if threads[idx] then
		threads[idx]._index = idx
	end
	threads[count] = nil
	self.ThreadCount = count - 1
	thread._index = nil
end

function LoopController:Destroy()
	self.Connection:Disconnect()
	for i = self.ThreadCount, 1, -1 do
		local thread = self.Threads[i]
		if thread then
			thread:Disable()
		end
		self.Threads[i] = nil
	end
	self.ThreadCount = 0
end

function ThreadController.new(rate, func, repeatTimes)
	return setmetatable({
		Rate = rate,
		Elapsed = 0,
		Finished = 0,
		RepeatTimes = repeatTimes,
		MainFunction = func,
		Disabled = false,
	}, ThreadController)
end

function ThreadController:handle(deltaTime)
	if self.Disabled then
		return
	end

	self.Elapsed = self.Elapsed + deltaTime
	if self.Elapsed < self.Rate then
		return
	end
	self.Elapsed = 0

	local repeatTimes = self.RepeatTimes
	if repeatTimes and self.Finished >= repeatTimes then
		self:Disable()
		return
	end

	local ok, err = pcall(self.MainFunction)
	if not ok then
		warn(err)
	end

	self.Finished = self.Finished + 1
end

function ThreadController:Disable()
	self.Disabled = true
	if self._owner then
		self._owner:removeThread(self)
	end
end

function ThreadController:Reset()
	self.Elapsed = 0
	self.Finished = 0
	self.Disabled = false
end

return LoopController
